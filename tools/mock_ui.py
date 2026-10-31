#!/usr/bin/env python3
"""Draw UI layout options with the firmware's own font and theme colours: build/ui/options.png."""
import re, math
from pathlib import Path
from PIL import Image, ImageDraw

ROOT = Path(__file__).resolve().parent.parent
H = (ROOT / "fw/firmware/gen/felucca_font.h").read_text()

def font(name):
    data = [int(x, 16) for x in re.search(rf"FONT_{name}_DATA\[\d+\] = \{{(.*?)\}};", H, re.S).group(1).split(",") if x.strip()]
    off = [int(x) for x in re.search(rf"FONT_{name}_OFF\[\d+\] = \{{(.*?)\}};", H).group(1).split(",")]
    adv = [int(x) for x in re.search(rf"FONT_{name}_ADV\[\d+\] = \{{(.*?)\}};", H).group(1).split(",")]
    bw = [int(x) for x in re.search(rf"FONT_{name}_BW\[\d+\] = \{{(.*?)\}};", H).group(1).split(",")]
    h, pad, first, last = [int(x) for x in re.search(rf"FONT_{name} = \{{ (\d+), (\d+), (\d+), (\d+)", H).groups()]
    return dict(data=data, off=off, adv=adv, bw=bw, h=h, pad=pad, first=first, last=last)

FS, FL = font("S"), font("L")

def text(img, x, y, f, s, col, align=0):
    px = img.load()
    def gi(ch):
        c = ord(ch)
        if 'a' <= ch <= 'z' and f["last"] < ord('a'): c -= 32
        if c < f["first"] or c > f["last"]: c = ord('?')
        return c - f["first"]
    w = sum(f["adv"][gi(ch)] for ch in s)
    if align == 1: x -= w // 2
    if align == 2: x -= w
    for ch in s:
        g = gi(ch); bw = f["bw"][g]; bpr = (bw + 1) // 2; base = f["off"][g]
        for gy in range(f["h"]):
            for gx in range(bw):
                v = f["data"][base + gy * bpr + gx // 2]
                v = v & 15 if gx & 1 else v >> 4
                if v:
                    X, Y = x - f["pad"] + gx, y + gy
                    if 0 <= X < 240 and 0 <= Y < 240:
                        bg = px[X, Y]; a = v / 15
                        px[X, Y] = tuple(int(bg[i] + (col[i] - bg[i]) * a) for i in range(3))
        x += f["adv"][g]
    return x

T = dict(bg=(26,15,28), hi=(247,232,238), mid=(168,138,160), dim=(67,40,74), acc=(255,143,177),
         lane=[(255,143,177),(255,198,109),(155,227,184),(160,168,255)])
LANES = [(4,16,"1/16","MAJOR","CSAW",[1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0],6),
         (5,8,"1/8","MAJOR","SQR SUB",[1,0,1,1,0,1,1,0],2),
         (7,16,"1/16","MAJOR","FM",[1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,0],11),
         (3,8,"1/12","MAJOR","FBK FM",[1,0,0,1,0,0,1,0],4)]

def steps(d, x, y, pat, cur, col, dim, w=6, h=10, gap=7, small=2):
    for k, hit in enumerate(pat):
        X = x + k * gap
        c = (255,255,255) if k == cur else (col if hit else dim)
        if hit: d.rectangle([X, y, X + w - 1, y + h - 1], fill=c)
        else: d.rectangle([X + w//2 - 1, y + h//2 - 1, X + w//2, y + h//2], fill=c)

def new():
    img = Image.new("RGB", (240, 240), T["bg"]); return img, ImageDraw.Draw(img)

# ---- A. LEDGER: current structure, cleaner. Underlined tabs, aligned columns, hairlines, right-aligned values.
def a_home():
    img, d = new()
    for i, g in enumerate(["HOME", "SEQ", "EDIT", "GLO"]):
        on = i == 0
        text(img, 8 + i * 50, 2, FS, g, T["hi"] if on else T["mid"])
        if on: d.rectangle([6 + i * 50, 18, 6 + i * 50 + 38, 19], fill=T["acc"])
    text(img, 234, 2, FS, "100", T["hi"], 2)
    d.line([0, 22, 239, 22], fill=T["dim"])
    for i, (h, s, sp, sc, snd, pat, cur) in enumerate(LANES):
        y = 28 + i * 36; col = T["lane"][i]
        if i == 0: d.rectangle([0, y - 2, 1, y + 30], fill=col)
        text(img, 8, y, FS, str(i + 1), col)
        steps(d, 24, y + 3, pat, cur, col, T["dim"])
        text(img, 8, y + 16, FS, f"{h}/{s} {sp}", col if i == 0 else T["mid"])
        text(img, 232, y + 16, FS, snd, col if i == 0 else T["mid"], 2)
        text(img, 150, y, FS, sc, T["mid"])
        d.line([8, y + 33, 231, y + 33], fill=T["dim"])
    d.line([0, 184, 239, 184], fill=T["dim"])
    text(img, 8, 190, FS, "P1", T["mid"]); text(img, 32, 190, FS, "INIT", T["hi"])
    text(img, 232, 190, FS, "KEY C", T["mid"], 2)
    text(img, 8, 212, FS, "1", T["lane"][0]); text(img, 32, 212, FS, "CSAW MID", T["lane"][0])
    text(img, 232, 212, FS, "OVERVIEW", T["acc"], 2)
    return img

def a_page():
    img, d = new()
    for i, g in enumerate(["HOME", "SEQ", "EDIT", "GLO"]):
        on = i == 1
        text(img, 8 + i * 50, 2, FS, g, T["hi"] if on else T["mid"])
        if on: d.rectangle([6 + i * 50, 18, 6 + i * 50 + 38, 19], fill=T["acc"])
    text(img, 234, 2, FS, "100", T["hi"], 2)
    d.line([0, 22, 239, 22], fill=T["dim"])
    for i, (h, s, sp, sc, snd, pat, cur) in enumerate(LANES):
        y = 28 + i * 18; col = T["lane"][i]
        text(img, 8, y, FS, str(i + 1), col if i == 0 else T["mid"])
        steps(d, 24, y + 4, pat, cur, col if i == 0 else T["dim"], T["dim"], 5, 8, 6)
    d.line([0, 102, 239, 102], fill=T["dim"])
    text(img, 8, 106, FS, "RHYTHM", T["acc"]); text(img, 232, 106, FS, "LANE 1", T["lane"][0], 2)
    cells = [("HITS", "4", 4/16), ("STEPS", "16", 0.5), ("SPEED", "1/16", 3/7), ("CHANCE", "100%", 1)]
    for k, (lab, val, f) in enumerate(cells):
        x = 8 + (k % 2) * 118; y = 126 + (k // 2) * 34
        text(img, x, y, FS, lab, T["mid"]); text(img, x + 108, y, FS, val, T["hi"], 2)
        d.rectangle([x, y + 17, x + 108, y + 18], fill=T["dim"]); d.rectangle([x, y + 17, x + int(108 * f), y + 18], fill=T["acc"])
    d.line([0, 198, 239, 198], fill=T["dim"])
    text(img, 8, 204, FS, "P1", T["mid"]); text(img, 32, 204, FS, "INIT", T["hi"]); text(img, 232, 204, FS, "KEY C", T["mid"], 2)
    text(img, 8, 222, FS, "1", T["lane"][0]); text(img, 32, 222, FS, "CSAW MID", T["lane"][0])
    return img

# ---- B. CARD: the chosen lane is a card with its values; the others are thin strips. Alfred peeks in a corner.
def alfred_small(img, x, y, scale=2):
    rows = (ROOT / "ui/alfred.txt").read_text().split()
    col = {'K':(10,5,12),'S':(238,190,150),'D':(205,150,115),'E':(20,20,30),'W':(240,236,226),'G':(150,150,160),'B':(52,30,62),'L':(104,70,122),'A':T["acc"]}
    px = img.load()
    for r, row in enumerate(rows):
        for c, ch in enumerate(row):
            if ch == '.': continue
            for dy in range(scale):
                for dx in range(scale):
                    X, Y = x + c * scale + dx, y + r * scale + dy
                    if 0 <= X < 240 and 0 <= Y < 240: px[X, Y] = col[ch]

def b_home():
    img, d = new()
    for i, g in enumerate(["HOME", "SEQ", "EDIT", "GLO"]):
        on = i == 0
        if on: d.rounded_rectangle([4 + i * 50, 2, 4 + i * 50 + 44, 19], 3, fill=T["acc"])
        text(img, 26 + i * 50, 2, FS, g, T["bg"] if on else T["mid"], 1)
    text(img, 234, 2, FS, "100", T["hi"], 2)
    for i, (h, s, sp, sc, snd, pat, cur) in enumerate(LANES):
        col = T["lane"][i]
        if i == 0:
            d.rounded_rectangle([4, 26, 235, 108], 5, outline=col, width=1)
            d.rectangle([4, 26, 235, 42], fill=col)
            text(img, 10, 27, FS, "LANE 1", T["bg"]); text(img, 230, 27, FS, snd, T["bg"], 2)
            steps(d, 14, 50, pat, cur, col, T["dim"], 8, 14, 13)
            for k, (lab, val) in enumerate([("HITS", str(h)), ("STEPS", str(s)), ("SPEED", sp), ("SCALE", sc)]):
                x = 12 + k * 56
                text(img, x, 72, FS, lab, T["mid"]); text(img, x, 88, FS, val, T["hi"])
        else:
            y = 116 + (i - 1) * 24
            text(img, 8, y + 2, FS, str(i + 1), col)
            steps(d, 24, y + 6, pat, cur, col, T["dim"], 5, 8, 6)
            text(img, 232, y + 2, FS, snd, T["mid"], 2)
    d.line([4, 190, 235, 190], fill=T["dim"])
    text(img, 8, 196, FS, "INIT", T["hi"]); text(img, 8, 214, FS, "KEY C  PENT+", T["mid"])
    alfred_small(img, 188, 176, 2)
    return img

def b_page():
    img, d = new()
    for i, g in enumerate(["HOME", "SEQ", "EDIT", "GLO"]):
        on = i == 1
        if on: d.rounded_rectangle([4 + i * 50, 2, 4 + i * 50 + 44, 19], 3, fill=T["acc"])
        text(img, 26 + i * 50, 2, FS, g, T["bg"] if on else T["mid"], 1)
    text(img, 234, 2, FS, "100", T["hi"], 2)
    for i, (h, s, sp, sc, snd, pat, cur) in enumerate(LANES):
        y = 26 + i * 14; col = T["lane"][i]
        steps(d, 8, y + 2, pat, cur, col if i == 0 else T["dim"], T["dim"], 5, 8, 6)
        text(img, 232, y - 2, FS, str(i + 1), col if i == 0 else T["dim"], 2)
    d.rounded_rectangle([4, 86, 235, 196], 5, outline=T["lane"][0], width=1)
    d.rectangle([4, 86, 235, 102], fill=T["lane"][0])
    text(img, 10, 87, FS, "RHYTHM", T["bg"]); text(img, 230, 87, FS, "LANE 1", T["bg"], 2)
    cells = [("HITS", "4", 4/16), ("STEPS", "16", 0.5), ("SPEED", "1/16", 3/7), ("CHANCE", "100%", 1)]
    for k, (lab, val, f) in enumerate(cells):
        x = 12 + (k % 2) * 114; y = 110 + (k // 2) * 42
        text(img, x, y, FS, lab, T["mid"]); text(img, x, y + 16, FS, val, T["hi"])
        d.rectangle([x, y + 34, x + 104, y + 36], fill=T["dim"]); d.rectangle([x, y + 34, x + int(104 * f), y + 36], fill=T["lane"][0])
    text(img, 8, 206, FS, "INIT", T["hi"]); text(img, 8, 222, FS, "1 CSAW MID", T["lane"][0])
    alfred_small(img, 188, 176, 2)
    return img

# ---- C. DIALS: four dials for the four knobs, lane strip above, big page title.
def dial(d, cx, cy, r, f, col, dim):
    d.arc([cx - r, cy - r, cx + r, cy + r], 135, 405, fill=dim, width=3)
    if f > 0: d.arc([cx - r, cy - r, cx + r, cy + r], 135, 135 + 270 * f, fill=col, width=3)
    a = math.radians(135 + 270 * f)
    d.line([cx, cy, cx + (r - 6) * math.cos(a), cy + (r - 6) * math.sin(a)], fill=col, width=2)

def c_page(page="RHYTHM", tab=1):
    img, d = new()
    for i, g in enumerate(["HOME", "SEQ", "EDIT", "GLO"]):
        on = i == tab
        text(img, 8 + i * 50, 2, FS, g, T["hi"] if on else T["dim"])
        if on: d.rectangle([6 + i * 50, 18, 6 + i * 50 + 38, 19], fill=T["acc"])
    text(img, 234, 2, FS, "100", T["hi"], 2)
    for i, (h, s, sp, sc, snd, pat, cur) in enumerate(LANES):
        y = 26 + i * 13; col = T["lane"][i]
        steps(d, 8, y + 2, pat, cur, col if i == 0 else T["dim"], T["dim"], 5, 7, 6)
        text(img, 232, y - 3, FS, str(i + 1), col if i == 0 else T["dim"], 2)
    text(img, 120, 82, FL, page, T["hi"], 1)
    cells = [("HITS", "4", 4/16), ("STEPS", "16", 0.5), ("SPEED", "1/16", 3/7), ("CHANCE", "100%", 1)]
    for k, (lab, val, f) in enumerate(cells):
        cx = 36 + k * 56
        dial(d, cx, 140, 20, f, T["lane"][0], T["dim"])
        text(img, cx, 164, FS, val, T["hi"], 1); text(img, cx, 180, FS, lab, T["mid"], 1)
    d.line([8, 204, 231, 204], fill=T["dim"])
    text(img, 8, 210, FS, "INIT", T["hi"]); text(img, 232, 210, FS, "1 CSAW MID", T["lane"][0], 2)
    return img

def c_home():
    img, d = new()
    for i, g in enumerate(["HOME", "SEQ", "EDIT", "GLO"]):
        on = i == 0
        text(img, 8 + i * 50, 2, FS, g, T["hi"] if on else T["dim"])
        if on: d.rectangle([6 + i * 50, 18, 6 + i * 50 + 38, 19], fill=T["acc"])
    text(img, 234, 2, FS, "100", T["hi"], 2)
    for i, (h, s, sp, sc, snd, pat, cur) in enumerate(LANES):
        y = 30 + i * 40; col = T["lane"][i]
        dial(d, 24, y + 14, 13, h / s, col, T["dim"])
        steps(d, 48, y + 2, pat, cur, col, T["dim"], 6, 10, 7)
        text(img, 48, y + 16, FS, f"{sp} {sc}", col if i == 0 else T["mid"])
        text(img, 232, y + 16, FS, snd, col if i == 0 else T["mid"], 2)
    d.line([8, 192, 231, 192], fill=T["dim"])
    text(img, 120, 198, FS, "INIT", T["hi"], 1); text(img, 120, 216, FS, "KEY C   OVERVIEW", T["mid"], 1)
    return img

# ---- D. COLUMNS: Mutable Dreams style. A tall meter per knob under the lane strip, bold title bar, status strip.
def d_page():
    img, d = new()
    d.rectangle([0, 0, 239, 20], fill=T["dim"])
    text(img, 6, 2, FS, "SEQ  RHYTHM", T["hi"]); text(img, 234, 2, FS, "100", T["hi"], 2)
    for i, (h, s, sp, sc, snd, pat, cur) in enumerate(LANES):
        y = 26 + i * 14; col = T["lane"][i]
        text(img, 6, y - 2, FS, str(i + 1), col if i == 0 else T["dim"])
        steps(d, 22, y + 2, pat, cur, col if i == 0 else T["dim"], T["dim"], 5, 8, 6)
        text(img, 232, y - 2, FS, snd, col if i == 0 else T["dim"], 2)
    cells = [("HITS", "4", 4/16), ("STEPS", "16", 0.5), ("SPEED", "1/16", 3/7), ("CHANCE", "100%", 1)]
    for k, (lab, val, f) in enumerate(cells):
        x = 10 + k * 58
        d.rectangle([x, 90, x + 46, 170], fill=(36, 22, 40))
        d.rectangle([x, 170 - int(80 * f), x + 46, 170], fill=T["lane"][0])
        text(img, x + 23, 176, FS, val, T["hi"], 1); text(img, x + 23, 192, FS, lab, T["mid"], 1)
    d.rectangle([0, 218, 239, 239], fill=T["dim"])
    text(img, 6, 221, FS, "INIT", T["hi"]); text(img, 234, 221, FS, "1 CSAW MID", T["lane"][0], 2)
    return img

def d_home():
    img, d = new()
    d.rectangle([0, 0, 239, 20], fill=T["dim"])
    text(img, 6, 2, FS, "FORMALFRED", T["hi"]); text(img, 234, 2, FS, "100", T["hi"], 2)
    for i, (h, s, sp, sc, snd, pat, cur) in enumerate(LANES):
        y = 28 + i * 46; col = T["lane"][i]
        d.rectangle([0, y, 3, y + 40], fill=col if i == 0 else T["dim"])
        text(img, 10, y, FS, f"{i + 1}  {snd}", col)
        text(img, 232, y, FS, f"{h}/{s}", T["mid"], 2)
        steps(d, 10, y + 18, pat, cur, col, T["dim"], 8, 14, 13)
    d.rectangle([0, 218, 239, 239], fill=T["dim"])
    text(img, 6, 221, FS, "INIT", T["hi"]); text(img, 234, 221, FS, "KEY C", T["mid"], 2)
    return img

OPTIONS = [("A. LEDGER", a_home(), a_page()), ("B. CARD", b_home(), b_page()), ("C. DIALS", c_home(), c_page()), ("D. COLUMNS", d_home(), d_page())]
sheet = Image.new("RGB", (2 * 250 + 10, len(OPTIONS) * 268 + 10), (30, 30, 30))
dr = ImageDraw.Draw(sheet)
for i, (name, home, page) in enumerate(OPTIONS):
    dr.text((10, 8 + i * 268), name, fill=(255, 255, 255))
    sheet.paste(home, (10, 22 + i * 268)); sheet.paste(page, (260, 22 + i * 268))
out = ROOT / "build/ui/options.png"; out.parent.mkdir(parents=True, exist_ok=True); sheet.save(out); print(out)
