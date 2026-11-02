#!/usr/bin/env python3
"""Render the five-minute pitch deck (site/pitch) into build/pitch: the theorem cards come from the proof index and
the film from tools/make_video.py. Open build/pitch/index.html in a browser; arrow keys move, N shows the notes. docs/PITCH.md is the
run-sheet. tools/make_site.py renders the same deck under the site at pitch/."""
import html, re, shutil, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
from proof_index import collect, sentence

def screen(out, name, ms, script):
    """The firmware's screen at `ms` after boot, driven by `script` (render_web.mjs's form), as a PNG at 3x,
    nearest-neighbour. Needs `make web` and Pillow."""
    frames = out / "frames"
    subprocess.run(["node", str(ROOT / "tools/frames.mjs"), str(ROOT / "build/web/dinghy.wasm"), str(frames), str(ms),
                    script], check=True)
    try:
        from PIL import Image
        raw = (frames / f"{ms}.raw").read_bytes()
        img = Image.new("RGB", (240, 240))
        px = img.load()
        for i in range(240 * 240):
            v = raw[2 * i] | raw[2 * i + 1] << 8
            px[i % 240, i // 240] = ((v >> 11) * 255 // 31, ((v >> 5) & 63) * 255 // 63, (v & 31) * 255 // 31)
        img.resize((720, 720), Image.NEAREST).save(out / name)
    except ImportError:
        pass
    shutil.rmtree(frames)

def home_screen(out):
    """The HOME screen at 4 s, the landing page's picture."""
    screen(out, "screen-home.png", 4000, "800:press:8")

def rhythm_screen(out):
    """SEQ > RHYTHM on LANTERNS' first lane, seven hits in sixteen drawn as a circle: the opening's picture."""
    screen(out, "screen-rhythm.png", 5200, "1500:patch:12,3000:press:11,3300:press:11")

def feature_screens(out):
    """The four pages of the features slide: NOTES on CLOCKWORK, FILTER on FACTORY's bass, REVERB, and PUNCH on FACTORY with
    CRUSH, STUTTER and WASH held. Buttons are the web build's: SEQ 11, EDIT 6, FX 2, REC 13."""
    screen(out, "screen-notes.png", 5200, "3000:press:11,3300:press:11,3600:press:11,3900:press:11")
    screen(out, "screen-filter.png", 5200, "1500:patch:14,3500:turn:0:1,3800:press:6,4100:press:6")
    screen(out, "screen-reverb.png", 5200, "1500:patch:14,3000:press:2,3300:press:2")
    screen(out, "screen-punch.png", 5200, "1500:patch:14,3000:press:13,3300:press:13,3600:key:8:1,3800:key:2:1,4000:key:9:1")

def card(claim, why, name):
    """A theorem card: the name, what it says, why it matters. Backticked names in the docstrings become code."""
    def prose(text):
        return re.sub(r"`([^`]+)`", r"<code>\1</code>", html.escape(text))
    return f'<code>{name}</code><p>{prose(claim)}</p>' + (f'<p class="why">{prose(why)}</p>' if why else "")

FILM = ROOT / "build/video/formalfred.webm"                      # tools/make_video.py; `make pitch` builds it first

def render(out, home=None):
    """Write the deck into `out`. `home` is an existing screen-home.png to copy; without one it is rendered."""
    out.mkdir(parents=True, exist_ok=True)
    index = collect()
    rows = {name: (claim, why) for _, name, claim, why, _ in index}
    per_module = {}
    for module, _, _, _, _ in index:
        per_module[module] = per_module.get(module, 0) + 1
    def theorem(m):
        """`{{theorem:name}}` is a full card; `{{claim:name}}` the name and the first sentence of what it says."""
        name = m.group(2)
        if name not in rows:
            sys.exit(f"pitch: no theorem {name} in Proofs/")
        claim, why = rows[name]
        return card(claim, why, name) if m.group(1) == "theorem" else card(sentence(claim), "", name)
    def count(m):
        """`{{count:A,B}}` is the theorems in modules A and B; `{{share:A,B}}` their share of all, in percent."""
        modules = m.group(2).split(",")
        missing = [x for x in modules if x not in per_module]
        if missing:
            sys.exit(f"pitch: no proof module {', '.join(missing)}")
        n = sum(per_module[x] for x in modules)
        return str(n) if m.group(1) == "count" else f"{100 * n / len(rows):.1f}"
    if not FILM.exists():
        sys.exit(f"pitch: {FILM} is missing; run make video first")
    shutil.copy(FILM, out / "formalfred.webm")
    values = {"theorems": str(len(rows)), "stamp": str(int(FILM.stat().st_mtime))}
    text = (ROOT / "site/pitch/index.html").read_text()
    kinds = {x for group in re.findall(r"\{\{count:([\w,]+)\}\}", text) for x in group.split(",")}
    unplaced = sorted(set(per_module) - kinds)
    if unplaced:                                                 # a new proof module goes into one of the five kinds
        sys.exit(f"pitch: proof module{'s' if len(unplaced) > 1 else ''} {', '.join(unplaced)} in no kind on the "
                 "'What is proved' slide")
    text = re.sub(r"\{\{(theorem|claim):(\w+)\}\}", theorem, text)
    text = re.sub(r"\{\{(count|share):([\w,]+)\}\}", count, text)
    for key, value in values.items():
        text = text.replace("{{" + key + "}}", value)
    left = sorted(set(re.findall(r"\{\{[^}]*\}\}", text)))
    if left:
        sys.exit(f"pitch: unfilled {' '.join(left)}")
    (out / "index.html").write_text(text)
    for name in ("pitch.css", "pitch.js"):
        shutil.copy(ROOT / "site/pitch" / name, out / name)
    shutil.copy(ROOT / "site/style.css", out / "style.css")
    shutil.copy(ROOT / "web/alfred.svg", out / "alfred.svg")
    shutil.copytree(ROOT / "site/pitch/scene", out / "scene", dirs_exist_ok=True)   # the FM-1 and the other firmwares
    if home and home.exists():
        shutil.copy(home, out / "screen-home.png")
    else:
        home_screen(out)
    rhythm_screen(out)
    feature_screens(out)
    return out / "index.html"

if __name__ == "__main__":
    print(render(ROOT / "build/pitch"))
