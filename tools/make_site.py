#!/usr/bin/env python3
"""Assemble the GitHub Pages site into build/site:
   index.html, the installer (with manifest.json and the .fwsc), and the simulator under sim/.
Run after `make web` and `make fw`.  tools/make_site.py [VERSION]"""
import hashlib, json, re, shutil, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "build/site"
version = sys.argv[1] if len(sys.argv) > 1 else "0.1.0"
shutil.rmtree(OUT, ignore_errors=True)
shutil.copytree(ROOT / "site", OUT)
shutil.copytree(ROOT / "build/web", OUT / "sim")
# the simulator page needs the isolation headers: load the service worker first
sim = OUT / "sim/index.html"
sim.write_text(sim.read_text().replace("<head>", '<head>\n<script src="../coi-serviceworker.min.js"></script>', 1))
pkg = ROOT / "fw/build/dinghy.fwsc"
data = pkg.read_bytes()
name = f"formalfred-{version}.fwsc"
(OUT / name).write_bytes(data)
product = re.search(r'PRODUCT = "(FM-1_\d+)"', (ROOT / "fw/tools/build.py").read_text()).group(1)
(OUT / "manifest.json").write_text(json.dumps({
    "name": "FORMALFRED", "version": version, "product": product, "size": len(data),
    "sha256": hashlib.sha256(data).hexdigest(), "package": name,
    "release_url": "https://github.com/mpancia/fmfm/releases"}, indent=1))
# the landing page: the firmware's own HOME screen at 4 s (a frame from the web build, nearest-neighbour at 2x),
# the theorem count and the groups from the proof index, the version
sys.path.insert(0, str(ROOT / "tools"))
from proof_index import collect, GROUPS
rows = collect()
by_module = {}
for mod, _, _, _ in rows:
    by_module[mod] = by_module.get(mod, 0) + 1
groups = "\n      ".join(
    f"<tr><td>{title}</td><td class=\"num\">{sum(by_module.get(m, 0) for m in mods)}</td><td>{about}</td></tr>"
    for title, about, mods in GROUPS if sum(by_module.get(m, 0) for m in mods))
index = OUT / "index.html"
index.write_text(index.read_text().replace("{{theorems}}", str(len(rows))).replace("{{groups}}", groups)
                 .replace("{{version}}", version))
frames = OUT / "frames"
subprocess.run(["node", str(ROOT / "tools/frames.mjs"), str(ROOT / "build/web/dinghy.wasm"), str(frames), "4000",
                "800:press:8"], check=True)
try:
    from PIL import Image
    raw = (frames / "4000.raw").read_bytes()
    img = Image.new("RGB", (240, 240))
    px = img.load()
    for i in range(240 * 240):
        v = raw[2 * i] | raw[2 * i + 1] << 8
        px[i % 240, i // 240] = ((v >> 11) * 255 // 31, ((v >> 5) & 63) * 255 // 63, (v & 31) * 255 // 31)
    img.resize((480, 480), Image.NEAREST).save(OUT / "screen-home.png")
except ImportError:
    pass
shutil.rmtree(frames)
# Alfred
try:
    from PIL import Image
    rows = (ROOT / "ui/alfred.txt").read_text().split()
    col = {'K':(10,5,12),'S':(238,190,150),'D':(205,150,115),'E':(20,20,30),'W':(240,236,226),'G':(150,150,160),'B':(52,30,62),'L':(104,70,122),'A':(255,143,177)}
    img = Image.new("RGBA", (24, 32), (0, 0, 0, 0))
    for y, r in enumerate(rows):
        for x, c in enumerate(r):
            if c != '.': img.putpixel((x, y), col[c] + (255,))
    img.save(OUT / "alfred.png")
except ImportError:
    pass
print(OUT, product, len(data))
