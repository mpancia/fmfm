#!/usr/bin/env python3
"""The Firmware Hub's card picture, docs/card.png: the HOME screen four seconds after power-on, 240 x 240, as the
chip draws it (RGB565 to RGB). Needs `make web` and Pillow. The hub's rules: square, 240 to 1024 px, PNG, 300 KB."""
import shutil, subprocess, sys
from pathlib import Path
from PIL import Image

ROOT = Path(__file__).resolve().parent.parent
frames = ROOT / "build/card"
subprocess.run(["node", str(ROOT / "tools/frames.mjs"), str(ROOT / "build/web/dinghy.wasm"), str(frames), "4000",
                "800:press:8"], check=True)
raw = (frames / "4000.raw").read_bytes()
img = Image.new("RGB", (240, 240))
px = img.load()
for i in range(240 * 240):
    v = raw[2 * i] | raw[2 * i + 1] << 8
    px[i % 240, i // 240] = ((v >> 11) * 255 // 31, ((v >> 5) & 63) * 255 // 63, (v & 31) * 255 // 31)
out = ROOT / (sys.argv[1] if len(sys.argv) > 1 else "docs/card.png")
img.save(out, optimize=True)
shutil.rmtree(frames)
print(out, img.size, out.stat().st_size, "B")
