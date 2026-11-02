#!/usr/bin/env python3
"""Render the five-minute pitch deck (site/pitch) into build/pitch: the theorem cards come from the proof index and
the demo videos from the web build. Open build/pitch/index.html in a browser; arrow keys move, N shows the notes. docs/PITCH.md is the
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

# The demos that run themselves: the simulator (the real firmware as wasm) driven by a script, recorded as a video
# for the deck. Button and encoder numbers are the web build's (fw/firmware/src/platform.c): HOME 8, SEQ 11, EDIT 6,
# ARP 10, PLAY 12, REC 13; SELECT is encoder 0, knob 1 encoder 2; key 0 is F3, so C4 is key 7. A step is (ms,
# actions, what the slide says at that moment, the theorem card it lights). Factory patches by index: ELECTRIC 11,
# NIGHT DRIVE 16. On the PUNCH page the keys are HALF 0, DOUBLE 1, STUTTER 2, ROLL 3, OCT- 4, OCT+ 5, SHIFT 6, GATE 7,
# CRUSH 8, WASH 9, THROW 10, BREAK 11, MUTE 1 to 4 are 12 to 15.

def held(at, key, ms, say=None, card=None):
    """A key held from `at` for `ms`; the cue goes with the press."""
    return [(at, [f"key:{key}:1"], say, card), (at + ms, [f"key:{key}:0"], None, None)]

def phrase(at, notes):
    """A line played on the keys: (key, length in ms) one after another, from `at`."""
    steps = []
    for key, ms in notes:
        steps += held(at, key, ms - 40)
        at += ms
    return steps

# ELECTRIC: the ballad on the FM voice. With QUANT on the white keys are the degrees of F major, so C4 (key 7) is F,
# E4 (11) is A, G4 (14) is C, A4 (16) is D, B4 (18) is E, C5 (19) is F.
ELECTRIC = [
    (1500, ["patch:11"], "ELECTRIC: an electric piano ballad on the FM voice written in Lean, I V vi IV in F. Nothing "
                         "is written down; the lanes choose every note.", None),
    (7000, ["press:10"], None, None),
    (7300, ["press:10"], None, None),
    (7600, ["turn:2:1"], "QUANT on, and a line played on the keys: the white keys are the degrees of F major, so "
                         "there is no wrong note to hit.", "keys_in_scale"),
    *phrase(8200, [(19, 700), (18, 700), (16, 1400), (14, 700), (16, 700), (18, 1400), (19, 700), (21, 700),
                   (19, 1400), (18, 700), (16, 2100)]),
    (20000, ["press:13"], "REC: the keys are effects. THROW sends the piano into the delay, WASH the reverb full up, "
                          "HALF time; let go and each is exactly as it was.", "punch_nothing_held_changes_nothing"),
    *held(20500, 10, 2500),
    *held(23500, 9, 3000),
    *held(27500, 0, 3000),
    (31000, ["press:13"], None, None),
    (37000, ["press:12"], "Stop. Silence at once; every note that started has been stopped.",
     "run_every_note_on_has_a_note_off"),
]

# NIGHT DRIVE: the electronic track. Lanes 2 and 4 held muted on the PUNCH page and let in one at a time, punch-ins, a
# drop on BREAK, the bass's filter swept on the FILTER page, DOUBLE and HALF time, stop.
NIGHT_DRIVE = [
    (1500, ["patch:16"], "NIGHT DRIVE: an 808 kick and snare, a filtered FM bass on a loop that mutates, a filtered "
                         "saw lead on a Markov chain, i VI III VII in A minor.", "run_bar_plays_every_hit"),
    (3600, ["press:13"], None, None),                 # buttons are ignored during Alfred's boot bow, until about 3.3 s
    (3700, ["key:13:1", "key:15:1"], "The snare and the lead taken out on the PUNCH page, and let back in one at a "
                                     "time.", None),
    (7500, ["key:15:0"], None, None),
    (11400, ["key:13:0"], None, None),
    *held(14000, 2, 1600, "STUTTER, GATE, CRUSH: each a key held, each gone the moment it is let go.",
          "punch_nothing_held_changes_nothing"),
    *held(16000, 7, 2000),
    *held(18500, 8, 1800),
    *held(20800, 11, 1700, "BREAK: every lane muted, then the drop."),
    (23000, ["press:13"], None, None),
    (23300, ["turn:0:2"], None, None),
    (23600, ["press:6"], None, None),
    (23900, ["press:6"], "The FILTER page on the bass: CUTOFF swept open and back. The filter's arithmetic is Lean, "
                         "its coefficients in range at every setting.", "filter_coefficients_in_range"),
    *[(24200 + i * 150, ["turn:2:2"], None, None) for i in range(20)],
    *[(27400 + i * 150, ["turn:2:-2"], None, None) for i in range(20)],
    (31000, ["press:13"], None, None),
    *held(31500, 1, 1600, "DOUBLE time, then HALF, then let go: the tempo is 100 again, exactly."),
    *held(33600, 0, 2000),
    (36000, ["press:13"], None, None),
    (38500, ["press:12"], "Stop.", "run_every_note_on_has_a_note_off"),
]

# THE WALKS: chord progressions that are group theory. TONNETZ (patch 7) walks L then R through all 24 triads; the
# HARMONY page (GLO, button 7) names the walk; HEXATONIC (8) is the P L cycle of six; BLACK KEYS (10) plays the
# complement of the key against the key.
WALKS = [
    (1500, ["patch:7"], "TONNETZ: the chord moves by L, then R, one note of the triad at a time, through all 24 major "
                        "and minor triads and back to the start. The three moves generate the dihedral group of "
                        "order 24; the lanes follow the triad.", "tonnetz_group_is_dihedral"),
    (4000, ["press:7"], None, None),
    (8000, ["press:8"], "Each move keeps two of the triad's three notes: voice leading, not jumps. The screen names "
                        "the chord as it changes.", "harmony_walk_keeps_two_notes"),
    (17000, ["patch:8"], "HEXATONIC: P then L, a cycle of six triads, bowed. The P R walk is a cycle of eight; "
                         "the L R walk one of 24.", "tonnetz_walks_are_cycles"),
    (29000, ["patch:10"], "BLACK KEYS: two lanes in C major, two on the five notes outside it. A six-note set and "
                          "its complement have the same intervals (Babbitt's hexachord theorem), so the black keys "
                          "are the white keys' shadow.", "harmony_hexachord_theorem"),
    (41000, ["press:12"], None, None),
]

DEMOS = {"walks": (WALKS, 44000), "electric": (ELECTRIC, 40000), "nightdrive": (NIGHT_DRIVE, 41000)}

def demo(out, name):
    """Render demo `name` as out/demo-<name>.webm (the screen at 30 fps with the sound; VP9 and Opus, which browsers
    without the H.264 codec still play) with a poster frame, and give the cues and the watch count."""
    steps, length = DEMOS[name]
    script = ",".join(f"{at}:{act}" for at, acts, _, _ in steps for act in acts)
    wav, raw, webm = out / f"demo-{name}.wav", out / f"demo-{name}.rgb565", out / f"demo-{name}.webm"
    run = subprocess.run(["node", str(ROOT / "tools/render_web.mjs"), str(ROOT / "build/web/dinghy.wasm"), str(wav),
                          str(length), script, str(raw), "30"], capture_output=True, text=True, check=True)
    watched = re.search(r"watched: (\d+) checks, (\d+) failed", run.stdout)
    subprocess.run(["ffmpeg", "-y", "-loglevel", "error", "-f", "rawvideo", "-pix_fmt", "rgb565le", "-s", "240x240",
                    "-r", "30", "-i", str(raw), "-i", str(wav), "-vf", "scale=720:720:flags=neighbor",
                    "-c:v", "libvpx-vp9", "-crf", "24", "-b:v", "0", "-c:a", "libopus", "-b:a", "128k",
                    "-shortest", str(webm)], check=True)
    subprocess.run(["ffmpeg", "-y", "-loglevel", "error", "-ss", "2", "-i", str(webm), "-frames:v", "1",
                    str(out / f"demo-{name}-poster.png")], check=True)
    raw.unlink(); wav.unlink()
    cues = "\n".join(f'<li data-at="{at / 1000}"' + (f' data-card="{theorem}"' if theorem else "") + f">{html.escape(say)}</li>"
                     for at, _, say, theorem in steps if say)
    checks = f"{int(watched.group(1)):,}" if watched else "?"
    return cues, checks, watched.group(2) if watched else "?", str(int(webm.stat().st_mtime))

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
    values = {"theorems": str(len(rows))}
    for name in DEMOS:                                           # cues:<demo>, checks:<demo>, fails:<demo>, stamp:<demo>
        cues, checks, fails, stamp = demo(out, name)
        values.update({f"cues:{name}": cues, f"checks:{name}": checks, f"fails:{name}": fails, f"stamp:{name}": stamp})
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
