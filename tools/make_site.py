#!/usr/bin/env python3
"""Assemble the GitHub Pages site into build/site:
   index.html, the installer (with manifest.json and the .fwsc), and the simulator under sim/.
Run after `make web` and `make fw`.  tools/make_site.py [VERSION]"""
import hashlib, json, re, shutil, sys
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
# Alfred for the landing page
sys.path.insert(0, str(ROOT / "tools"))
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
