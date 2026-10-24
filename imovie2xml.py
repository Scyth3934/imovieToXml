#!/usr/bin/env python3
"""Convert iMovie 10 projects (inside a .imovielibrary) to FCP7 XML (xmeml v4) for Premiere Pro.

Usage:
  python3 imovie2xml.py LIBRARY.imovielibrary --list
  python3 imovie2xml.py LIBRARY.imovielibrary --project "Name" --out OUTDIR
  python3 imovie2xml.py LIBRARY.imovielibrary --all --out OUTDIR

Converted: primary-storyline clips, connected clips (cutaways / picture-in-picture on V2+,
music and sound effects on A2+), compound clips (flattened), transitions (as Cross Dissolve,
with an audio cross fade where both sides have sound), speed changes (constant speed; ramps
and freeze frames become the average speed so the first and last frames still match),
reverse, crop / Ken Burns, rotation, clip volume and fades, project fade in/out, markers,
and titles (rendered to transparent PNGs with FFmpeg).
Not converted: transition styles other than dissolves, color and video filters, title
animation, green screen, split screen.
"""
import argparse, glob, json, os, plistlib, re, shutil, sqlite3, subprocess, sys, tempfile
from fractions import Fraction as Fr
from urllib.parse import quote
from xml.sax.saxutils import escape

FFMPEG = '/usr/local/bin/ffmpeg' if os.path.exists('/usr/local/bin/ffmpeg') else shutil.which('ffmpeg')
FFPROBE = '/usr/local/bin/ffprobe' if os.path.exists('/usr/local/bin/ffprobe') else shutil.which('ffprobe')


# ---------- reading the Core Data store ----------

def unarchive(b):
    p = plistlib.loads(b)
    if not isinstance(p, dict) or p.get('$archiver') != 'NSKeyedArchiver':
        return p
    objs = p['$objects']

    def dec(x):
        if isinstance(x, plistlib.UID):
            x = objs[x.data]
        if isinstance(x, dict):
            if 'NS.keys' in x:
                return {dec(k): dec(v) for k, v in zip(x['NS.keys'], x['NS.objects'])}
            if 'NS.objects' in x:
                return [dec(v) for v in x['NS.objects']]
            for k in ('NS.time', 'NS.string', 'NS.data'):
                if k in x:
                    return x[k]
            if '$classname' in x:
                return None
            return {k: dec(v) for k, v in x.items() if k != '$class'}
        if x == '$null':
            return None
        return x
    return dec(p['$top']['root'])


def ozml_strings(raw):
    """All embedded OZML (Motion XML) documents inside a metadata blob."""
    out = []

    def scan(x):
        if isinstance(x, bytes):
            if x.startswith(b'<?xml'):
                out.append(x.decode('utf8', 'replace'))
            elif x.startswith(b'bplist'):
                try:
                    scan(plistlib.loads(x))
                except Exception:
                    pass
        elif isinstance(x, dict):
            for v in x.values():
                scan(v)
        elif isinstance(x, list):
            for v in x:
                scan(v)
    if raw:
        scan(plistlib.loads(raw))
    return out


class Store:
    def __init__(self, path):
        self.path = path
        tmp = tempfile.mkdtemp()
        shutil.copy(path, os.path.join(tmp, 'db'))  # read a copy; iMovie may hold a lock
        self.db = sqlite3.connect(os.path.join(tmp, 'db'))
        self.O = {}
        for pk, t, n, ident in self.db.execute('select Z_PK,ZTYPE,ZNAME,ZIDENTIFIER from ZCOLLECTION'):
            self.O[pk] = {'pk': pk, 'type': t, 'name': n, 'id': ident, 'children': [], 'parents': [], 'md': None, 'raw': None}
        for c, b in self.db.execute('select ZCOLLECTION,ZDICTIONARYDATA from ZCOLLECTIONMD'):
            if b and c in self.O:
                self.O[c]['raw'] = b
                try:
                    self.O[c]['md'] = unarchive(b)
                except Exception:
                    pass
        for p, c in self.db.execute('select Z_3PARENTCOLLECTIONS,Z_3CHILDCOLLECTIONS from Z_3CHILDCOLLECTIONS'):
            self.O[p]['children'].append(c)
            self.O[c]['parents'].append(p)
        self.db.close()
        shutil.rmtree(tmp, ignore_errors=True)

    def md(self, o):
        return o['md'] if isinstance(o['md'], dict) else {}

    def rel(self, o, name):
        for c in o['children']:
            c = self.O[c]
            if c['type'] in ('NSSet', 'NSArray') and c['name'] == name:
                ch = [self.O[x] for x in c['children']]
                order = self.md(c).get('$order')
                if order:
                    pos = {i: n for n, i in enumerate(order)}
                    ch.sort(key=lambda x: pos.get(x['id'], 1e9))
                return ch
        return []

    def oz(self, o):
        return ozml_strings(o['raw'])

    def effects(self, o, kind):
        out = []
        for st in self.rel(o, kind):
            for k in ('intrinsicEffects', 'effects'):
                out += self.rel(st, k)
        return out


def rng(s):
    return [Fr(int(x), int(y)) for x, y in re.findall(r'\((-?\d+)/(\d+)\)', s)]


def frac(s):
    try:
        a, b = s.split('/')
        return Fr(int(a), int(b))
    except (ValueError, AttributeError, ZeroDivisionError):
        return None  # iMovie writes 'invalid' for an unused fade


# ---------- library-wide lookups ----------

def load_library(lib):
    """Open every event database once. Returns (stores, media index by mediaIdentifier)."""
    stores = [Store(ev) for ev in glob.glob(os.path.join(glob.escape(lib), '**', 'CurrentVersion.imovieevent'), recursive=True)]
    media = {}
    for st in stores:
        evdir = os.path.dirname(st.path)
        for o in st.O.values():
            if o['type'] != 'FFMediaRep':
                continue
            md = st.md(o)
            rel = md.get('projectRelativePath')
            if not rel:
                continue
            path = os.path.join(evdir, rel)
            if not os.path.exists(path):
                # iMovie sometimes renames a file to "name (fcp1).ext" and keeps the old path
                stem, ext = os.path.splitext(path)
                alt = glob.glob(glob.escape(stem) + ' (fcp*)' + glob.escape(ext))
                if not alt:
                    continue
                path = alt[0]
            for s in o['parents']:
                for a in st.O[s]['parents']:
                    amd = st.md(st.O[a])
                    mid = amd.get('mediaIdentifier')
                    if not mid:
                        continue
                    # clip ranges are in the media's own timecode; keep its start to rebase in/out points
                    start = (rng(amd['mediaRange']) or [Fr(0)])[0] if amd.get('mediaRange') else Fr(0)
                    # an original file beats an optimized/proxy copy
                    if md.get('repType') == 'originalMediaRep' or mid not in media:
                        media[mid] = (os.path.realpath(path), start)
    return stores, media


def find_projects(stores):
    out = []
    for st in stores:
        for o in st.O.values():
            md = st.md(o)
            if o['type'] == 'FFAnchoredCollection' and md.get('isProject'):
                out.append((md.get('displayName'), o['pk'], st))
    return out


# ---------- interpreting the edit ----------

def volume(st, o):
    for stack in st.rel(o, 'audioEffects'):
        for s in st.oz(stack):
            m = re.search(r'name="Volume".*?<curve[^>]*value="([^"]+)"', s, re.S)
            if m:
                fi = re.search(r'<fadeInOffset>(\d+) (\d+)', s)
                fo = re.search(r'<fadeOutOffset>(\d+) (\d+)', s)
                return (float(m.group(1)),
                        Fr(int(fi.group(1)), int(fi.group(2))) if fi else Fr(0),
                        Fr(int(fo.group(1)), int(fo.group(2))) if fo else Fr(0))
    return 1.0, Fr(0), Fr(0)


def retime(st, o, a, d):
    """Source time at the clip's first and last frame, and whether the speed varies inside it.

    The Time Map curve maps clip time to source time; a falling curve means reverse.
    """
    for e in st.effects(o, 'videoEffects'):
        if st.md(e).get('effectID') == 'FFRetime':
            s = st.oz(e)[0]
            tm = s[s.find('name="Time Map"'):s.find('name="Speed"')]
            kps = [(Fr(int(x), int(y)), Fr(v)) for x, y, v in
                   re.findall(r'<time>(\d+) (\d+) \d+ \d+</time>\s*<value>([^<]+)</value>', tm)]
            if len(kps) < 2:
                break

            def at(t):
                for (t0, v0), (t1, v1) in zip(kps, kps[1:]):
                    if t <= t1:
                        break
                return v0 + (v1 - v0) / (t1 - t0) * (t - t0)
            inside = [t for t, _ in kps if a < t < a + d]
            slopes = {(v1 - v0) / (t1 - t0) for (t0, v0), (t1, v1) in zip(kps, kps[1:])
                      if t1 > a and t0 < a + d}
            return at(a), at(a + d), bool(inside) and len(slopes) > 1
    return a, a + d, False


def kenburns(st, o):
    for e in st.effects(o, 'videoEffects'):
        if st.md(e).get('effectID') == 'HECrop':
            s = st.oz(e)[0]
            m = re.search(r'name="Type".*?value="(\d+)"', s, re.S)
            typ = int(m.group(1)) if m else 1  # older projects store only the fill rectangle
            # Insets are in percent of frame HEIGHT for all four sides. Each side is a curve of
            # (seconds from clip start, value). The first group (ids 1-4) is the plain crop, the
            # second (ids 6-9) the fill/Ken Burns rectangle used when Type is 1.
            sides = {}
            for name, pid in re.findall(r'<parameter name="(Left|Right|Top|Bottom)" id="(\d+)"', s):
                blk = s[s.find(f'name="{name}" id="{pid}"'):]
                blk = blk[:blk.find('</parameter>')]
                kps = [(Fr(int(x), int(y)), float(v)) for x, y, v in
                       re.findall(r'<time>(\d+) (\d+) \d+ \d+</time>\s*<value>([^<]+)</value>', blk)]
                cur = float(re.search(r'value="([^"]+)"', blk).group(1))
                sides.setdefault(name, []).append(kps or [(Fr(0), cur)])
            # Type 0 = plain crop, 1 = crop to fill (static), 2 = Ken Burns (start -> end over the clip).
            # Types 1 and 2 use the second group, measured on the frame-filling image.
            group = 1 if typ in (1, 2) else 0
            keys = {k: v[group] if len(v) > group else v[0] for k, v in sides.items()}
            if len(keys) != 4:
                continue
            if typ == 1:
                return {'mode': 'fill', 'keys': {k: [kps[0]] for k, kps in keys.items()}}
            if typ == 2:
                # the end keyframe sits at a 24-hour sentinel; iMovie plays it across the clip
                return {'mode': 'kenburns', 'keys': keys, 'span': True}
            if any(val for kps in keys.values() for _, val in kps):
                return {'mode': 'crop', 'keys': keys}
    return None


def curve_at(kps, t):
    if t <= kps[0][0] or len(kps) == 1:
        return kps[0][1]
    for (t0, v0), (t1, v1) in zip(kps, kps[1:]):
        if t <= t1:
            return v0 + (v1 - v0) * float((t - t0) / (t1 - t0))
    return kps[-1][1]


def rotation(st, o):
    for c in st.rel(o, 'containedItems') + [o]:
        if 'rotationAngle' in st.md(c):
            return float(st.md(c)['rotationAngle'])
    return 0.0


def components(st, o):
    """Media components of a clip: the collection's own, or the item itself."""
    if o['type'] == 'FFAnchoredMediaComponent':
        return [o]
    return [c for c in st.rel(o, 'containedItems') if c['type'] == 'FFAnchoredMediaComponent']


def is_clip(st, o):
    if o['type'] == 'FFAnchoredMediaComponent':
        return True
    kids = st.rel(o, 'containedItems')
    return bool(kids) and all(c['type'] == 'FFAnchoredMediaComponent' for c in kids)


def media_ref(st, o):
    for c in components(st, o):
        for m in st.rel(c, 'media'):
            return st.md(m).get('mediaIdentifier'), st.md(m).get('displayName')
    return None, None


def streams(st, o):
    """(has_video, has_audio) for a clip, counting the audio anchored to its video component."""
    v = a = False
    for c in components(st, o):
        key = st.md(c).get('providerSourceKey', '')
        v |= key.startswith('v')
        a |= key.startswith('a')
        for x in st.rel(c, 'anchoredItems'):
            a |= st.md(x).get('providerSourceKey', '').startswith('a')
    return v, a


SOLIDS = {'black': '000000', 'white': 'FFFFFF', 'blue': '1F4E9A', 'red': 'B3261E', 'green': '2E7D32', 'yellow': 'F2C230',
          'orange': 'E8772E', 'purple': '6A3FA0', 'pink': 'E68FB0', 'gray': '808080', 'grey': '808080'}


def title_info(st, o):
    """(text lines, title template name, solid colour) for a generator. Only its own effects are read,
    not clips connected to it."""
    lines, template, solid = [], None, None
    seen, stack = set(), [o]
    while stack:
        x = stack.pop()
        if x['pk'] in seen:
            continue
        seen.add(x['pk'])
        md = st.md(x)
        if x['type'] == 'FFMotionEffect' and md.get('effectType') == 'effect.video.title':
            template = md.get('displayName', '') or 'Title'
        if 'SolidColor' in x['type'] or str(md.get('effectID', '')).startswith('ConsumerSolid'):
            name = md.get('displayName', '').lower()
            solid = next((v for k, v in SOLIDS.items() if k in name), '808080')
        if x['type'] == 'FFMotionEffectValue':
            for s in st.oz(x):
                for txt in re.findall(r'<text>(.*?)</text>', s, re.S):
                    size = re.search(r'name="(?:Line \d )?Size"[^>]*value="([^"]+)"', s)
                    lines.append({'text': txt.strip(), 'size': float(size.group(1)) if size else 72})
        for c in x['children']:
            c = st.O[c]
            if c['type'] in ('NSSet', 'NSArray') and c['name'] in ('anchoredItems', 'containedItems', 'persistedAnchoredObject'):
                continue
            stack.append(c)
    return [l for l in lines if l['text']], template, solid


def extract(st, root):
    """Flatten the project into placed items (seconds on the project timeline).

    lane 0 is the primary storyline, positive lanes are connected video above it,
    negative lanes connected audio below it.
    """
    items, markers, notes = [], [], []

    def clamp(T, d, window):
        """Visible part of [T, T+d] inside a compound clip's window: (start, dur, head trimmed)."""
        if window is None:
            return T, d, Fr(0)
        s, e = max(T, window[0]), min(T + d, window[1])
        return s, e - s, s - T

    def add(it, T, a, d, lane, window):
        md = st.md(it)
        name = (md.get('displayName') or '').strip()
        s, vis, head = clamp(T, d, window)
        if vis <= 0:
            return
        if it['type'] in ('FFAnchoredCollection', 'FFAnchoredMediaComponent') and is_clip(st, it):
            mid, mname = media_ref(st, it)
            has_v, has_a = streams(st, it)
            s0, s1, ramp = retime(st, it, a, d)
            k = (s1 - s0) / d if d else Fr(1)
            v, fi, fo = volume(st, it)
            items.append({'kind': 'clip', 'start': s, 'dur': vis, 'lane': lane, 'media_id': mid, 'name': mname or name,
                          'src0': s0 + head * k, 'src1': s0 + (head + vis) * k, 'ramp': ramp, 'video': has_v,
                          'audio': has_a, 'volume': v, 'fade_in': fi if not head else Fr(0),
                          'fade_out': fo if head + vis == d else Fr(0), 'motion': kenburns(st, it),
                          'rotation': rotation(st, it)})
        elif it['type'] == 'FFAnchoredCollection':
            # compound clip: its inner time x sits at T + (x - a); only [T, T+d] is visible
            inner = (s, s + vis)
            place(it, T - a, lane, inner)
        elif it['type'] == 'FFAnchoredGeneratorComponent':
            lines, template, solid = title_info(st, it)
            if template is None and solid is None or template is not None and not lines and solid is None:
                notes.append(f'generator "{name}" at {float(T):.2f}s skipped (no text or colour found)')
            else:
                items.append({'kind': 'title', 'start': s, 'dur': vis, 'lane': lane, 'lines': lines,
                              'template': template or '', 'solid': solid, 'name': name})
        elif it['type'] not in ('FFAnchoredGapGeneratorComponent',):
            notes.append(f'{it["type"]} "{name}" at {float(T):.2f}s skipped')

    def place(container, shift, lane, window=None):
        kids = st.rel(container, 'containedItems')
        t = frac(st.md(container).get('unclippedStart', '0/1')) or Fr(0)
        for i, it in enumerate(kids):
            md = st.md(it)
            if 'clippedRange' not in md:
                continue
            a, d = rng(md['clippedRange'])
            T = t + shift
            if it['type'] == 'FFAnchoredTransition':
                # transitions overlap their neighbours; they take no time on the storyline
                edge = 'start' if i == 0 else 'end' if i == len(kids) - 1 else 'center'
                if window is None or window[0] <= T <= window[1]:
                    items.append({'kind': 'transition', 'start': T, 'dur': d, 'lane': lane, 'edge': edge,
                                  'name': (md.get('displayName') or '').strip()})
                continue
            add(it, T, a, d, lane, window)
            for an in st.rel(it, 'anchoredItems'):
                m = st.md(an)
                ap = rng(m.get('anchorPair', '{(0/1),(0/1)}'))  # (child time, parent time)
                if an['type'] == 'FFAnchoredTimeMarker':
                    if window is None:
                        markers.append({'start': T + (ap[1] - a), 'name': m.get('displayName', '')})
                    continue
                if 'clippedRange' not in m:
                    continue
                r = rng(m['clippedRange'])
                child_lane = m.get('anchoredLane', 0)
                add(an, T + (ap[1] - a) - (ap[0] - r[0]), r[0], r[1], lane or child_lane, window)
            t += d

    place(root, Fr(0), 0)
    fades = [st.md(f) for f in st.rel(root, 'fades')]
    end = max([x['start'] + x['dur'] for x in items if x['kind'] != 'transition'] + [Fr(0)])
    return {'duration': end, 'items': items, 'markers': markers, 'fades': fades, 'notes': notes}


# ---------- writing xmeml ----------

_probe_cache = {}


def probe(path):
    if path not in _probe_cache:
        j = json.loads(subprocess.run([FFPROBE, '-v', 'error', '-print_format', 'json', '-show_format', '-show_streams', path],
                                      capture_output=True, text=True).stdout or '{}')
        ss = j.get('streams', [])
        still = path.lower().endswith(('.png', '.jpg', '.jpeg', '.heic', '.tif', '.tiff'))
        v = next((s for s in ss if s['codec_type'] == 'video' and (still or s.get('disposition', {}).get('attached_pic') != 1)), None)
        a = next((s for s in ss if s['codec_type'] == 'audio'), None)
        dur = j.get('format', {}).get('duration')
        rot = 0
        for sd in (v or {}).get('side_data_list', []):
            rot = int(sd.get('rotation', rot) or 0)
        rot = rot or int((v or {}).get('tags', {}).get('rotate', 0) or 0)
        still = still or (v is not None and a is None and (not dur or float(dur) < 0.1))
        _probe_cache[path] = {'video': v is not None, 'width': v and v.get('width'), 'height': v and v.get('height'),
                              'still': still,
                              'upright': abs(rot) % 180 == 90,  # stored sideways; players (and Premiere) turn it
                              'channels': a and a.get('channels'), 'samplerate': a and a.get('sample_rate'),
                              'duration': Fr(dur) if dur and not still else Fr(3600)}
    return _probe_cache[path]


class Writer:
    def __init__(self, fps_num, fps_den, width, height):
        self.num, self.den = fps_num, fps_den
        self.tb = round(fps_num / fps_den)
        self.ntsc = 'TRUE' if fps_den == 1001 else 'FALSE'
        self.w, self.h = width, height
        self.files = {}
        self.n = 0

    def f(self, t):
        return int(round(Fr(t) * self.num / self.den))

    def rate(self):
        return f'<rate><timebase>{self.tb}</timebase><ntsc>{self.ntsc}</ntsc></rate>'

    def file_el(self, path):
        if path in self.files:
            return f'<file id="{self.files[path]}"/>'
        info = probe(path)
        fid = f'file-{len(self.files) + 1}'
        self.files[path] = fid
        url = 'file://localhost' + quote(path, safe='/')
        media = ''
        if info['video']:
            media += (f'<video><samplecharacteristics>{self.rate()}<width>{info["width"]}</width>'
                      f'<height>{info["height"]}</height><anamorphic>FALSE</anamorphic>'
                      f'<pixelaspectratio>square</pixelaspectratio><fielddominance>none</fielddominance>'
                      f'</samplecharacteristics></video>')
        if info['channels']:
            media += (f'<audio><samplecharacteristics><depth>16</depth><samplerate>{info["samplerate"]}</samplerate>'
                      f'</samplecharacteristics><channelcount>{info["channels"]}</channelcount></audio>')
        return (f'<file id="{fid}"><name>{escape(os.path.basename(path))}</name><pathurl>{url}</pathurl>'
                f'{self.rate()}<duration>{self.f(info["duration"])}</duration><timecode>{self.rate()}<string>00:00:00:00</string>'
                f'<frame>0</frame><displayformat>NDF</displayformat></timecode><media>{media}</media></file>')

    def cid(self):
        self.n += 1
        return f'clipitem-{self.n}'


def param(pid, name, value, vmin=None, vmax=None, keys=None):
    s = f'<parameter authoringApp="PremierePro"><parameterid>{pid}</parameterid><name>{name}</name>'
    if vmin is not None:
        s += f'<valuemin>{vmin}</valuemin><valuemax>{vmax}</valuemax>'
    s += f'<value>{value}</value>'
    for when, val in keys or []:
        s += f'<keyframe><when>{when}</when><value>{val}</value></keyframe>'
    return s + '</parameter>'


def effect(name, eid, cat, etype, mediatype, params):
    return (f'<filter><effect><name>{name}</name><effectid>{eid}</effectid><effectcategory>{cat}</effectcategory>'
            f'<effecttype>{etype}</effecttype><mediatype>{mediatype}</mediatype>{params}</effect></filter>')


def crop_rect(W, c, t, img):
    """iMovie crop/Ken Burns rectangle at clip time t, in output pixels: (left, top, width, height).

    The insets are percent of frame HEIGHT, measured from the edges of the clip as iMovie first
    fits it inside the frame (img = fitted width, height).
    """
    k = c['motion']['keys']
    if c['motion'].get('span'):
        # Ken Burns: first keyframe at the clip's start, last at its end
        f = Fr(t) / c['dur'] if c['dur'] else Fr(0)
        k = {n: [(Fr(0), kps[0][1]), (Fr(1), kps[-1][1])] for n, kps in k.items()}
        t = f
    u = W.h / 100
    iw, ih = img
    ox, oy = (W.w - iw) / 2, (W.h - ih) / 2
    l, r = curve_at(k['Left'], t) * u, curve_at(k['Right'], t) * u
    tp, b = curve_at(k['Top'], t) * u, curve_at(k['Bottom'], t) * u
    return ox + l, oy + tp, iw - l - r, ih - tp - b


def fit_scale(W, info, c):
    """iMovie first fits every clip inside the frame; Premiere imports XML clips at 100%, so write it.

    Returns (scale, fitted width, fitted height).
    """
    sw, sh = info['width'], info['height']
    if info.get('upright'):
        sw, sh = sh, sw
    if int(abs(c['rotation'])) % 180 == 90:
        sw, sh = sh, sw
    f = min(W.w / sw, W.h / sh)
    return f, sw * f, sh * f


def motion_filter(W, c, cin, cout, fit):
    """Fit, rotation and crop rectangle -> Basic Motion scale / center / rotation.

    The crop rectangle is zoomed to fill the frame width. Center is written as an offset from
    frame centre in fractions of the frame size.
    """
    f, iw, ih = fit

    def sc(t):
        if not c['motion']:
            return f * 100, 0.0, 0.0
        l, tp, w, h = crop_rect(W, c, t, (iw, ih))
        if w <= 0 or h <= 0:
            return f * 100, 0.0, 0.0
        z = max(W.w / w, W.h / h)
        cx = (W.w / 2 - (l + w / 2)) * z
        cy = (W.h / 2 - (tp + h / 2)) * z
        return z * f * 100, cx / W.w, cy / W.h
    s0, x0, y0 = sc(Fr(0))
    s1, x1, y1 = sc(c['dur'])
    moving = (round(s0, 3), round(x0, 5), round(y0, 5)) != (round(s1, 3), round(x1, 5), round(y1, 5))
    center = lambda x, y: f'<horiz>{x:.6f}</horiz><vert>{y:.6f}</vert>'
    p = param('scale', 'Scale', f'{s0:.4f}', 0, 1000, [(cin, f'{s0:.4f}'), (cout, f'{s1:.4f}')] if moving else None)
    p += (f'<parameter authoringApp="PremierePro"><parameterid>center</parameterid><name>Center</name>'
          f'<value>{center(x0, y0)}</value>')
    if moving:
        p += (f'<keyframe><when>{cin}</when><value>{center(x0, y0)}</value></keyframe>'
              f'<keyframe><when>{cout}</when><value>{center(x1, y1)}</value></keyframe>')
    p += '</parameter>'
    if c['rotation']:
        # iMovie angles are counter-clockwise; Premiere's are clockwise
        p += param('rotation', 'Rotation', f'{-c["rotation"]:.1f}', -8640, 8640)
    return effect('Basic Motion', 'basic', 'motion', 'motion', 'video', p)


def opacity_filter(keys):
    return effect('Opacity', 'opacity', 'motion', 'motion', 'video', param('opacity', 'opacity', 100, 0, 100, keys))


def speed_filter(speed, reverse, mediatype):
    p = (param('variablespeed', 'variablespeed', 0, 0, 1) + param('speed', 'speed', f'{speed * 100:.4f}', -100000, 100000)
         + param('reverse', 'reverse', 'TRUE' if reverse else 'FALSE') + param('frameblending', 'frameblending', 'FALSE'))
    return effect('Time Remap', 'timeremap', 'motion', 'motion', mediatype, p)


def level_filter(v, keys=None):
    return effect('Audio Levels', 'audiolevels', 'audiolevels', 'audiolevels', 'audio',
                  param('level', 'Level', f'{v:.5f}', 0, 3.98109, keys))


def transition_el(W, st, en, align, mediatype):
    if mediatype == 'video':
        eff = ('<name>Cross Dissolve</name><effectid>Cross Dissolve</effectid><effectcategory>Dissolve</effectcategory>'
               '<effecttype>transition</effecttype><mediatype>video</mediatype><wipecode>0</wipecode>'
               '<wipeaccuracy>100</wipeaccuracy><startratio>0</startratio><endratio>1</endratio><reverse>FALSE</reverse>')
    else:
        eff = ('<name>Cross Fade (+3dB)</name><effectid>KGAudioTransCrossFade3dB</effectid><effectcategory>Dissolve</effectcategory>'
               '<effecttype>transition</effecttype><mediatype>audio</mediatype>')
    return (f'<transitionitem>{W.rate()}<start>{st}</start><end>{en}</end><alignment>{align}</alignment>'
            f'<effect>{eff}</effect></transitionitem>')


_font = None


def title_font():
    global _font
    if _font is None:
        _font = os.path.join(tempfile.gettempdir(), 'imovie2xml_GillSansBold.ttf')
        if not os.path.exists(_font):
            try:
                from fontTools.ttLib import TTCollection
                for fnt in TTCollection('/System/Library/Fonts/Supplemental/GillSans.ttc').fonts:
                    if fnt['name'].getDebugName(4) == 'Gill Sans Bold':
                        fnt.save(_font)
            except Exception:
                _font = '/System/Library/Fonts/Supplemental/Arial Bold.ttf'
    return _font


def render_title(t, W, outpath):
    """Render a title's text to a transparent PNG: centred, at the bottom for lower thirds, mid-frame otherwise.

    Sizes are iMovie's point sizes on a 1080-line frame.
    """
    k = W.h / 1080
    lines = []
    for l in t['lines']:
        for sub in l['text'].splitlines() or ['']:
            lines.append((sub, max(8, int(l['size'] * k))))
    gap = [int(s * 1.35) for _, s in lines]
    lower = 'lower' in t['template'].lower() or 'third' in t['template'].lower()
    y = int(957 * k) - sum(gap[:-1]) if lower else int((W.h - sum(gap)) / 2)
    dt = []
    for (txt, size), g in zip(lines, gap):
        txt = txt.replace('\\', '\\\\').replace("'", '’').replace(':', '\\:').replace('%', '\\%')
        dt.append(f"drawtext=fontfile='{title_font()}':text='{txt}':fontsize={size}:fontcolor=white:"
                  f"shadowcolor=black@0.6:shadowx=2:shadowy=2:x=(w-text_w)/2:y={y}")
        y += g
    bg = f'color=0x{t["solid"]}:s={W.w}x{W.h},format=rgba' if t.get('solid') else f'color=black@0.0:s={W.w}x{W.h},format=rgba'
    subprocess.run([FFMPEG, '-v', 'error', '-y', '-f', 'lavfi', '-i', bg,
                    '-vf', ','.join(dt) or 'null', '-frames:v', '1', outpath], check=True)


def pack(groups, n_fixed=0):
    """Assign (start, end, payload) items to tracks; groups are packed in order, each on the first free track."""
    tracks = [[] for _ in range(n_fixed)]
    for first, group in groups:
        for s, e, p in sorted(group, key=lambda x: x[0]):
            for ti in range(first, len(tracks) + 1):
                if ti == len(tracks):
                    tracks.append([])
                if all(e <= s2 or s >= e2 for s2, e2, _ in tracks[ti]):
                    tracks[ti].append((s, e, p))
                    break
    return [sorted(t, key=lambda x: x[0]) for t in tracks]


def build_xml(name, E, W, media, title_dir, safe):
    notes = list(E['notes'])
    total = W.f(E['duration'])
    fades = E['fades'][0] if E['fades'] else {}
    fin = W.f(frac(fades.get('fadeInDuration')) or 0)
    fout = W.f(frac(fades.get('fadeOutDuration')) or 0)

    # merge contiguous pieces of the same audio-only source (iMovie splits music at every edit)
    items = []
    for c in sorted(E['items'], key=lambda x: (x['lane'], x['start'])):
        p = items[-1] if items else None
        if (c['kind'] == 'clip' and not c['video'] and p and p['kind'] == 'clip' and not p['video']
                and p['lane'] == c['lane'] and p['media_id'] == c['media_id'] and p['volume'] == c['volume']
                and not p['fade_out'] and not c['fade_in'] and p['src1'] - p['src0'] == p['dur'] and c['src1'] - c['src0'] == c['dur']
                and abs(p['start'] + p['dur'] - c['start']) < Fr(1, 1000) and abs(p['src1'] - c['src0']) < Fr(1, 1000)):
            p['dur'] += c['dur']
            p['src1'] = c['src1']
            p['fade_out'] = c['fade_out']
        else:
            items.append(dict(c))

    vgroups, agroups = {}, {}
    spine_v = sorted([c for c in items if c['lane'] == 0 and c['kind'] in ('clip', 'title') and (c['kind'] == 'title' or c['video'])],
                     key=lambda c: c['start'])
    first_v, last_v = (spine_v[0], spine_v[-1]) if spine_v else (None, None)
    for c in items:
        if c['kind'] == 'transition':
            continue
        st, en = W.f(c['start']), W.f(c['start'] + c['dur'])
        if en <= st:
            continue
        if c['kind'] == 'title':
            png = os.path.join(title_dir, f'{safe} - title {W.n + 1:03d}.png')
            render_title(c, W, png)
            vid = W.cid()
            keys = []
            if c is first_v and fin:
                keys += [(0, 0), (fin, 100)]
            if c is last_v and fout:
                keys += [(en - st - fout, 100), (en - st, 0)]
            label = ' / '.join(l['text'] for l in c['lines']) or c['name'] or 'Solid'
            xml = (f'<clipitem id="{vid}"><name>{escape(label)}</name><enabled>TRUE</enabled><duration>{en - st}</duration>'
                   f'{W.rate()}<start>{st}</start><end>{en}</end><in>0</in><out>{en - st}</out>{W.file_el(png)}'
                   f'{opacity_filter(keys) if keys else ""}</clipitem>')
            vgroups.setdefault(c['lane'], []).append((st, en, {'id': vid, 'xml': xml}))
            continue
        if c['media_id'] not in media:
            notes.append(f'media not found: {c["name"]} at {float(c["start"]):.2f}s')
            continue
        path, tc_start = media[c['media_id']]
        info = probe(path)
        lo, hi = min(c['src0'], c['src1']) - tc_start, max(c['src0'], c['src1']) - tc_start
        reverse = c['src1'] < c['src0']
        cin, cout = W.f(lo), W.f(hi)
        if info.get('still'):
            # iMovie parks stills an hour into an endless clip; Premiere wants them from 0
            cin, cout, reverse = 0, en - st, False
        elif cout <= cin:
            cout = cin + 1
            notes.append(f'{c["name"]} at {float(c["start"]):.2f}s is a freeze frame; made a 1-frame slow clip')
        speed = (cout - cin) / (en - st)
        if c['ramp']:
            notes.append(f'{c["name"]} at {float(c["start"]):.2f}s has a speed ramp; used its average speed {speed * 100:.0f}%')
        fdur = W.f(info['duration'])
        if cin < 0 or cout > fdur + 1:
            notes.append(f'{c["name"]} at {float(c["start"]):.2f}s uses frames outside its file ({cin}-{cout} of {fdur})')
        retimed = abs(speed - 1) > 0.005 or reverse
        has_v = c['video'] and info['video']
        has_a = c['audio'] and bool(info['channels'])
        vid = W.cid() if has_v else None
        aid = W.cid() if has_a else None
        common = f'<duration>{fdur}</duration>{W.rate()}<start>{st}</start><end>{en}</end><in>{cin}</in><out>{cout}</out>'
        if has_v:
            filt = speed_filter(speed, reverse, 'video') if retimed else ''
            fit = fit_scale(W, info, c)
            if c['motion'] or c['rotation'] or abs(fit[0] - 1) > 1e-4:
                filt += motion_filter(W, c, cin, cout, fit)
            keys = []
            if c is first_v and fin:
                keys += [(cin, 0), (cin + fin, 100)]
            if c is last_v and fout:
                keys += [(cout - fout, 100), (cout, 0)]
            if keys:
                filt += opacity_filter(keys)
            xml = (f'<clipitem id="{vid}"><name>{escape(c["name"])}</name><enabled>TRUE</enabled>{common}'
                   f'{W.file_el(path)}{filt}%LINKS%</clipitem>')
            vgroups.setdefault(c['lane'], []).append((st, en, {'id': vid, 'xml': xml, 'link': aid}))
        if has_a:
            keys = []
            if c['fade_in']:
                keys += [(cin, 0), (cin + W.f(c['fade_in']), f'{c["volume"]:.5f}')]
            if c['fade_out']:
                keys += [(cout - W.f(c['fade_out']), f'{c["volume"]:.5f}'), (cout, 0)]
            filt = (speed_filter(speed, reverse, 'audio') if retimed else '') + level_filter(c['volume'], keys)
            xml = (f'<clipitem id="{aid}" premiereChannelType="stereo"><name>{escape(c["name"])}</name><enabled>TRUE</enabled>'
                   f'{common}{W.file_el(path)}<sourcetrack><mediatype>audio</mediatype><trackindex>1</trackindex></sourcetrack>'
                   f'{filt}%LINKS%</clipitem>')
            agroups.setdefault(c['lane'], []).append((st, en, {'id': aid, 'xml': xml, 'link': vid}))

    # V1 = storyline, then connected video by lane; A1 = storyline sound, then connected
    # video's sound, then audio lanes nearest the storyline first
    vtracks = pack([(0, vgroups.get(0, []))] + [(1, vgroups[l]) for l in sorted(vgroups) if l != 0], 1)
    alanes = sorted((l for l in agroups if l != 0), key=lambda l: (l < 0, abs(l)))
    atracks = pack([(0, agroups.get(0, []))] + [(1, agroups[l]) for l in alanes], 1)

    where = {}
    for kind, tracks in (('video', vtracks), ('audio', atracks)):
        for ti, t in enumerate(tracks, 1):
            for ci, (_, _, p) in enumerate(t, 1):
                where[p['id']] = (kind, ti, ci)

    def links(p):
        if not p.get('link') or p['link'] not in where:
            return ''
        out = ''
        for n, cid in enumerate(sorted([p['id'], p['link']], key=lambda x: where[x][0] != 'video'), 1):
            kind, ti, ci = where[cid]
            out += (f'<link><linkclipref>{cid}</linkclipref><mediatype>{kind}</mediatype><trackindex>{ti}</trackindex>'
                    f'<clipindex>{ci}</clipindex>' + (f'<groupindex>1</groupindex>' if kind == 'audio' else '') + '</link>')
        return out

    # transitions on the storyline: centred on the cut, or fades from/to black at either end
    trans = {'video': [], 'audio': []}
    for c in items:
        if c['kind'] != 'transition':
            continue
        d = W.f(c['dur'])
        cut = W.f(c['start'])
        if d <= 0:
            continue
        if c['lane'] != 0:
            notes.append(f'transition inside a connected clip at {float(c["start"]):.2f}s not converted')
            continue
        if c['edge'] == 'start':
            span, align = (cut, cut + d), 'start-black'
        elif c['edge'] == 'end':
            span, align = (cut - d, cut), 'end-black'
        else:
            span, align = (cut - d // 2, cut - d // 2 + d), 'center'
        trans['video'].append((span, align))
        a1 = atracks[0] if atracks else []
        if align == 'center' and any(e == cut for _, e, _ in a1) and any(s == cut for s, _, _ in a1):
            trans['audio'].append((span, align))
        if c['name'] and 'dissolve' not in c['name'].lower():
            notes.append(f'transition "{c["name"]}" at {float(c["start"]):.2f}s became a Cross Dissolve')

    def track_xml(t, kind, ti):
        els = [(s, 0, p['xml'].replace('%LINKS%', links(p))) for s, _, p in t]
        if ti == 1:
            els += [(span[0], -1, transition_el(W, span[0], span[1], align, kind)) for span, align in trans[kind]]
        return '<track>' + ''.join(x for _, _, x in sorted(els, key=lambda x: (x[0], x[1]))) + '</track>'

    markers = ''.join(f'<marker><name>{escape(m["name"])}</name><in>{W.f(m["start"])}</in><out>-1</out></marker>'
                      for m in sorted(E['markers'], key=lambda m: m['start']))
    fmt = (f'<format><samplecharacteristics>{W.rate()}<width>{W.w}</width><height>{W.h}</height>'
           f'<anamorphic>FALSE</anamorphic><pixelaspectratio>square</pixelaspectratio>'
           f'<fielddominance>none</fielddominance></samplecharacteristics></format>')
    xml = ('<?xml version="1.0" encoding="UTF-8"?>\n<!DOCTYPE xmeml>\n<xmeml version="4">'
           f'<sequence id="sequence-1"><name>{escape(name)}</name><duration>{total}</duration>{W.rate()}'
           f'<timecode>{W.rate()}<string>00:00:00:00</string><frame>0</frame><displayformat>NDF</displayformat></timecode>'
           f'<media><video>{fmt}' + ''.join(track_xml(t, 'video', i) for i, t in enumerate(vtracks, 1)) + '</video>'
           f'<audio><numOutputChannels>2</numOutputChannels><format><samplecharacteristics><depth>16</depth>'
           f'<samplerate>48000</samplerate></samplecharacteristics></format>'
           + ''.join(track_xml(t, 'audio', i) for i, t in enumerate(atracks, 1)) +
           f'</audio></media>{markers}</sequence></xmeml>\n')
    return xml, notes


def convert(name, pk, st, media, outdir):
    info = st.md(st.O[pk])
    frd = info.get('videoProps', {}).get('FRD') or {'value': 1001, 'timescale': 60000}
    pb = re.findall(r'\d+', info.get('videoProps', {}).get('PB', '{{0, 0}, {1920, 1080}}'))
    E = extract(st, st.O[pk])
    os.makedirs(outdir, exist_ok=True)
    W = Writer(frd['timescale'], frd['value'], int(pb[2]), int(pb[3]))
    safe = re.sub(r'[/:\\?*"<>|]', '-', name).strip() or 'Untitled'
    xml, notes = build_xml(name, E, W, media, outdir, safe)
    out = os.path.join(outdir, f'{safe}.xml')
    with open(out, 'w') as fh:
        fh.write(xml)
    return out, notes


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('library')
    ap.add_argument('--project')
    ap.add_argument('--all', action='store_true', help='convert every project in the library')
    ap.add_argument('--out', default='.')
    ap.add_argument('--list', action='store_true')
    a = ap.parse_args()
    stores, media = load_library(a.library)
    projects = find_projects(stores)
    if a.list or not (a.project or a.all):
        for n, _, _ in projects:
            print(n)
        return
    todo = projects if a.all else [p for p in projects if p[0] == a.project]
    if not todo:
        sys.exit(f'project not found: {a.project}')
    for name, pk, st in todo:
        out, notes = convert(name, pk, st, media, a.out)
        print(out)
        for n in notes:
            print('  note:', n)


if __name__ == '__main__':
    main()
