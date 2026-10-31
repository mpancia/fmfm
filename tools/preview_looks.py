#!/usr/bin/env python3
"""Render every look of the firmware (ui/theme.h) as a contact sheet: the startup screen mid-bow, the home page,
and a settings page. Builds one web variant per look, so it takes a minute.

  tools/preview_looks.py [OUT.png]          default build/looks.png
"""
import re
import subprocess
import sys
from pathlib import Path

from PIL import Image, ImageDraw

ROOT = Path(__file__).resolve().parent.parent
names = re.findall(r'\{"([A-Z ]+)", RGB', (ROOT / "ui/theme.h").read_text())
# boot at 1700 ms is mid-bow; the line is typed out by 2900; the app starts at 3000. Then HOME, then SEQ twice.
SHOTS = [1000, 1800, 2900, 3600, 4400]
SCRIPT = "3300:press:8,4000:press:11,4100:press:11"


def rgb565(data):
    img = Image.new("RGB", (240, 240))
    px = img.load()
    for i in range(240 * 240):
        v = data[2 * i] | data[2 * i + 1] << 8
        px[i % 240, i // 240] = ((v >> 11) * 255 // 31, ((v >> 5) & 63) * 255 // 63, (v & 31) * 255 // 31)
    return img


def main():
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / "build/looks.png"
    cols = [1800, 3600, 4400]
    sheet = Image.new("RGB", (len(cols) * 250 + 10, len(names) * 270 + 10), (30, 30, 30))
    draw = ImageDraw.Draw(sheet)
    for i, name in enumerate(names):
        variant = ROOT / f"build/looks/{i}"
        variant.mkdir(parents=True, exist_ok=True)
        subprocess.run(["sh", "tools/build_web.sh"], cwd=ROOT, check=True, capture_output=True,
                       env={**__import__("os").environ, "WEB_OUT": f"build/looks/{i}", "WEB_DEFS": f"-DALFRED_LOOK={i}"})
        subprocess.run(["node", "tools/frames.mjs", f"build/looks/{i}/dinghy.wasm", f"build/looks/{i}/f",
                        ",".join(map(str, SHOTS)), SCRIPT], cwd=ROOT, check=True)
        draw.text((10, 10 + i * 270), f"{i + 1}. {name}", fill=(255, 255, 255))
        for j, t in enumerate(cols):
            frame = rgb565((variant / "f" / f"{t}.raw").read_bytes())
            sheet.paste(frame, (10 + j * 250, 24 + i * 270))
    sheet.save(out)
    print(out)


if __name__ == "__main__":
    main()
