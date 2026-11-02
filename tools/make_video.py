#!/usr/bin/env python3
"""The demo film, about a minute and a half: build/video/formalfred.mp4 (and .webm). One song made of four presets
played at once: four runs of the simulator (the firmware as WebAssembly, tools/render_web.mjs), one a stem, all
started at the same instant in the same key and tempo and mixed as the arrangement brings them in and out: the pad,
then the keys, then the 808 with the filtered FM bass under a line played on the keys, then a flute lead for the
lift, then down to the pad again. The four screens in a grid, each lit while its stem sounds; chapter cards with a theorem on the
right, in the deck's look. Needs `make web`, ffmpeg and Pillow.  tools/make_video.py"""
import subprocess, sys
from pathlib import Path
from PIL import Image, ImageDraw, ImageFont

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "build/video"
sys.path.insert(0, str(ROOT / "tools"))
from proof_index import collect, sentence

def held(at, key, ms, say=None, card=None):
    """A key held from `at` for `ms`."""
    return [(at, [f"key:{key}:1"], say, card), (at + ms, [f"key:{key}:0"], None, None)]

def phrase(at, notes):
    """A line played on the keys: (key, length in ms) one after another, from `at`."""
    out = []
    for key, ms in notes:
        out += held(at, key, ms - 40)
        at += ms
    return out

# F major at 108, vi IV I V a chord a bar, four bars a cycle of 8.89 s. Every stem loads its patch at the same moment,
# so their chords stay in step. Patches by index: STEM PAD 17, KEYS 18, DRUMS 19, LEAD 20. Buttons: LFO 5, EDIT 6,
# HOME 8, ARP 10, PLAY 12, REC 13; SELECT is encoder 0, knobs 1 to 3 are encoders 2 to 4. The FILTER page (EDIT twice)
# moves CUTOFF by 2 a detent and RESO by 2; the LFO page's knobs are TARGET (OFF CHANCE LEVEL TIMBRE COLOUR), RATE in
# bars and DEPTH by 5. Buttons are ignored during the boot bow, so the first press is at 3.6 s. With QUANT on in F
# major the white keys are the degrees from C4 (key 7): 11 A, 14 C, 16 D, 18 E, 19 F, 21 G.
START, CYCLE, LENGTH = 1500, 8889, 78000
def cycle(k):
    return (START + k * CYCLE) / 1000
C1, C2, C3, C4, C5, C6, C7 = (cycle(k) for k in range(1, 8))
END = LENGTH / 1000
BEAT = 556                                                            # ms, at 108

def steps(*parts):
    return [(at, acts) for part in parts for at, acts, *_ in part]

def sweep(at, detents, every):
    """CUTOFF turned by `detents` (+ or -) one detent at a time, one every `every` ms, from `at`."""
    sign = 1 if detents > 0 else -1
    return [(at + i * every, [f"turn:2:{sign}"], None, None) for i in range(abs(detents))]

def filter_page(at, lane):
    """SELECT to `lane` (0 to 3, from lane 0) and the FILTER page."""
    return [(at, [f"turn:0:{lane}"] if lane else [], None, None), (at + 200, ["press:6"], None, None),
            (at + 500, ["press:6"], None, None)]

def lfo(at, lane, target, rate, depth):
    """SELECT to `lane` and the LFO page: TARGET (1 CHANCE 2 LEVEL 3 TIMBRE 4 COLOUR), RATE 0 to 4, DEPTH in percent."""
    return [(at, [f"turn:0:{lane}"] if lane else [], None, None), (at + 200, ["press:5"], None, None),
            (at + 500, [f"turn:2:{target}", f"turn:3:{rate}", f"turn:4:{depth // 5}"], None, None)]

# A stem: the patch, what its run does, when it sounds (a gain over time, as an ffmpeg expression in t), its place in
# the grid. The fades are the same windows the gains use, so a screen lights as its stem comes in.
STEMS = {
    "pad": {
        "patch": 17, "cell": (0, 0),
        "steps": steps([(START, ["patch:17"])],
                       filter_page(3600, 0), [(4200, ["turn:2:-36"])],                      # the glass pad's cutoff to 28
                       sweep(4500, 36, 480),                                                  # opening over two cycles
                       lfo(C3 * 1000, 3, 3, 1, 40),                                           # the pluck's timbre, slowly
                       [(C3 * 1000 + 1000, ["press:8"]), (75000, ["press:12"])]),             # home; stop: Alfred
        "on": [(0, END)],
        "gain": f"if(lt(t,3),t/3,if(lt(t,{C7 + 2}),1,max(0,({END - 1}-t)/{END - 1 - C7 - 2})))",
    },
    "keys": {
        "patch": 18, "cell": (1, 0),
        "steps": steps([(START, ["patch:18"])],
                       lfo(3600, 1, 4, 1, 35),                                                # the arpeggio's colour
                       [(4600, ["press:8"])],
                       [(C2 * 1000 - 1000, ["turn:0:-1"]), (C2 * 1000 - 800, ["press:10"]), (C2 * 1000 - 500, ["press:10"]),
                        (C2 * 1000 - 200, ["turn:2:1"])],                                     # QUANT on, the piano chosen
                       phrase(C2 * 1000 + 1100, [(19, BEAT), (18, BEAT), (16, 2 * BEAT), (14, BEAT), (16, BEAT),
                                                 (18, 2 * BEAT), (19, BEAT), (21, BEAT), (19, 2 * BEAT), (18, BEAT),
                                                 (16, 3 * BEAT)]),
                       phrase(C3 * 1000 + 1100, [(14, BEAT), (16, BEAT), (18, 2 * BEAT), (21, BEAT), (19, BEAT),
                                                 (18, 2 * BEAT), (16, BEAT), (14, BEAT), (11, 4 * BEAT)]),
                       [(C6 * 1000 - 2600, ["press:13"])],
                       held(C6 * 1000 - 2400, 10, 2200),                                      # THROW into the delay
                       [(C6 * 1000, ["press:13"]), (C7 * 1000, ["press:12"])]),
        "on": [(C1, C7)],
        "gain": f"if(lt(t,{C1}),0,if(lt(t,{C1 + 1}),(t-{C1})*0.85,if(lt(t,{C7}),0.85,max(0,0.85*({C7 + 2}-t)/2))))",
    },
    "drums": {
        "patch": 19, "cell": (0, 1),
        "steps": steps([(START, ["patch:19"])],
                       filter_page(3600, 3), [(4200, ["turn:3:12", "turn:2:-30"])],           # the bass: RESO up, CUTOFF to 42
                       sweep(C2 * 1000, 29, 300),                                             # opening across a cycle
                       sweep(C5 * 1000, -29, 300),                                            # and closing before the end
                       [(C4 * 1000 - 1500, ["press:13"])],
                       held(C4 * 1000 - 1300, 11, 1300),                                      # BREAK, then the lift
                       [(C4 * 1000 + 300, ["press:13"]), (C4 * 1000 + 600, ["press:6"]),   # EDIT remembers FILTER
                        (C6 * 1000 - 2600, ["press:13"])],
                       held(C6 * 1000 - 2400, 0, 2300),                                       # HALF time out
                       [(C6 * 1000, ["press:12"])]),
        "on": [(C2, C6)],
        "gain": f"if(lt(t,{C2}),0,if(lt(t,{C6}),0.8,0))",
    },
    "lead": {
        "patch": 20, "cell": (1, 1),
        "steps": steps([(START, ["patch:20"])],
                       filter_page(3600, 0), [(4200, ["turn:3:10", "turn:2:-40"])],           # the flute: RESO up, CUTOFF to 20
                       lfo(5000, 1, 2, 2, 50),                                                # the glass line breathes
                       [(5600, ["turn:0:-1"]), (5800, ["press:6"])],                           # back to the flute's filter
                       sweep(C4 * 1000, 40, 150),                                             # opened as it comes in
                       sweep(C5 * 1000 + 4000, -20, 200),                                     # half closed again
                       [(C6 * 1000 + 1500, ["press:12"])]),
        "on": [(C4, C6 + 1)],
        "gain": f"if(lt(t,{C4}),0,if(lt(t,{C6}),0.8,max(0,0.8*({C6 + 2}-t)/2)))",
    },
}

# The cards: (from s, to s, label, headline, body, theorem or None). The first is the title, the last the close.
CARDS = [
    (0, 8, "", "FORMALFRED", "A generative sequencer for the M-VAVE FM-1, its promises proved in Lean. One song, "
     "four presets playing at once.", None),
    (8, C1, "the pad", "Four lanes, each a rhythm choosing its own notes.",
     "vi IV I V in F. A plucked line walks the scale; the pad's filter opens over two cycles. Nothing is written "
     "down.", "lane_note_in_scale"),
    (C1, C2, "the keys", "A four-operator FM voice, written in Lean.",
     "A second preset, in step with the first: the piano on the chord, an arpeggio climbing it with an LFO on its "
     "colour.", "fm_sine_bounded"),
    (C2, C4, "the drums", "An 808 kit and a filtered FM bass, in Lean, under a line played on the keys.",
     "The bass's filter, resonant, sweeps open across a cycle. The keys are quantized to F major: there is no wrong "
     "note to hit.", "keys_in_scale"),
    (C4, C6, "the lift", "BREAK held, let go on the one; a flute on a Markov chain comes in.",
     "A fourth preset over the other three, its filter opening as it enters, an LFO breathing the glass line. Four "
     "runs, four clocks, never a tick apart.", "run_clock_never_drifts"),
    (C6, C7, "down", "THROW on the piano, HALF time on the drums, the bass's filter closing; each let go.",
     "There is no effect state, only the keys.", "punch_nothing_held_changes_nothing"),
    (C7, END, "", "Stop.", "Every note that started has been stopped; the pad plays itself out.\n\n"
     "mpancia.github.io/fmfm\nmake install && make run", "run_every_note_on_has_a_note_off"),
]

ROSE, INK, GREY = (226, 61, 110), (0, 0, 0), (85, 85, 85)
FONTS = "/usr/share/fonts/liberation/"
CELL, GAP, GRID_X, GRID_Y = 420, 20, 80, 190                     # the four screens, two by two

def font(name, size):
    return ImageFont.truetype(FONTS + name, size)

def wrap(draw, text, f, width):
    lines = []
    for paragraph in text.split("\n"):
        line = ""
        for word in paragraph.split():
            trial = (line + " " + word).strip()
            if draw.textlength(trial, font=f) > width and line:
                lines.append(line); line = word
            else:
                line = trial
        lines.append(line)
    return lines

def card(path, label, headline, body, theorem, rows):
    """A 860 x 720 transparent card: the label, the headline, the body, the theorem's name and first sentence."""
    img = Image.new("RGBA", (860, 720), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    y = 0
    if label:
        d.text((0, y), label.upper(), font=font("LiberationMono-Regular.ttf", 20), fill=GREY); y += 44
    if headline == "FORMALFRED":
        f = font("LiberationSans-Regular.ttf", 112)
        d.text((0, y), "FORM", font=f, fill=INK)
        d.text((d.textlength("FORM", font=f), y), "ALFRED", font=f, fill=ROSE); y += 140
    else:
        f = font("LiberationSans-Bold.ttf", 42)
        for line in wrap(d, headline, f, 860):
            d.text((0, y), line, font=f, fill=INK); y += 52
    y += 16
    f = font("LiberationSans-Regular.ttf", 28)
    for line in wrap(d, body, f, 860):
        d.text((0, y), line, font=f, fill=INK); y += 38
    if theorem:
        y += 24
        d.line((0, y, 860, y), fill=(216, 216, 216), width=1); y += 18
        d.text((0, y), theorem, font=font("LiberationMono-Regular.ttf", 23), fill=ROSE); y += 38
        f = font("LiberationSans-Regular.ttf", 23)
        for line in wrap(d, sentence(rows[theorem]), f, 860):
            d.text((0, y), line, font=f, fill=GREY); y += 31
    img.save(path)

def render(name, stem):
    """A stem's run: the screen as raw RGB565 at 30 fps and the sound as WAV."""
    script = ",".join(f"{int(at)}:{act}" for at, acts in stem["steps"] for act in acts)
    wav, raw = OUT / f"{name}.wav", OUT / f"{name}.rgb565"
    subprocess.run(["node", str(ROOT / "tools/render_web.mjs"), str(ROOT / "build/web/dinghy.wasm"), str(wav),
                    str(LENGTH), script, str(raw), "30"], check=True, capture_output=True, text=True)
    return wav, raw

def main():
    OUT.mkdir(parents=True, exist_ok=True)
    rows = {name: claim for _, name, claim, _, _ in collect()}
    for _, _, _, _, _, theorem in CARDS:
        if theorem and theorem not in rows:
            sys.exit(f"video: no theorem {theorem}")
    cards = []
    for i, (a, b, label, headline, body, theorem) in enumerate(CARDS):
        path = OUT / f"card{i}.png"
        card(path, label, headline, body, theorem, rows)
        cards.append((a, b, path))
    names = list(STEMS)
    runs = {name: render(name, STEMS[name]) for name in names}
    inputs = []
    for name in names:
        inputs += ["-f", "rawvideo", "-pix_fmt", "rgb565le", "-s", "240x240", "-r", "30", "-i", str(runs[name][1])]
    for name in names:
        inputs += ["-i", str(runs[name][0])]
    for _, _, path in cards:
        inputs += ["-loop", "1", "-t", str(END), "-i", str(path)]
    n = len(names)
    chain = [f"color=c=0xf6f8f7:s=1920x1080:r=30:d={END}[bg]"]
    last = "bg"
    for i, name in enumerate(names):
        stem = STEMS[name]
        (a, b), = stem["on"]
        fades = f",fade=in:st={a}:d=1:alpha=1" + (f",fade=out:st={b}:d=1:alpha=1" if b < END else "")
        chain.append(f"[{i}:v]scale={CELL}:{CELL}:flags=neighbor,format=rgba,colorchannelmixer=aa=0.25[d{i}]")
        chain.append(f"[{i}:v]scale={CELL}:{CELL}:flags=neighbor,format=rgba{fades}[s{i}]")
        x, y = GRID_X + stem["cell"][0] * (CELL + GAP), GRID_Y + stem["cell"][1] * (CELL + GAP)
        chain.append(f"[{last}][d{i}]overlay={x}:{y}[g{i}]")                  # the screen, dim, always
        chain.append(f"[g{i}][s{i}]overlay={x}:{y}[v{i}]")                    # and lit while the stem sounds
        last = f"v{i}"
    for i, (a, b, _) in enumerate(cards):
        chain.append(f"[{2 * n + i}:v]format=rgba,fade=in:st={a}:d=0.6:alpha=1,fade=out:st={b - 0.6}:d=0.6:alpha=1[c{i}]")
        chain.append(f"[{last}][c{i}]overlay=1000:190:enable='between(t,{a},{b})'[k{i}]")
        last = f"k{i}"
    for i, name in enumerate(names):
        chain.append(f"[{n + i}:a]volume='{STEMS[name]['gain']}':eval=frame[a{i}]")
    chain.append("".join(f"[a{i}]" for i in range(n)) + f"amix=inputs={n}:normalize=0,volume=1.6,alimiter=limit=0.95[a]")
    graph = ";".join(chain)
    for codec, name in ((["-c:v", "libx264", "-crf", "18", "-pix_fmt", "yuv420p", "-c:a", "aac", "-b:a", "192k"], "formalfred.mp4"),
                        (["-c:v", "libvpx-vp9", "-crf", "28", "-b:v", "0", "-c:a", "libopus", "-b:a", "128k"], "formalfred.webm")):
        subprocess.run(["ffmpeg", "-y", "-loglevel", "error", *inputs, "-filter_complex", graph, "-map", f"[{last}]",
                        "-map", "[a]", "-t", str(END), *codec, str(OUT / name)], check=True)
    for wav, raw in runs.values():
        raw.unlink(); wav.unlink()
    for _, _, path in cards:
        path.unlink()
    print(OUT / "formalfred.mp4")

if __name__ == "__main__":
    main()
