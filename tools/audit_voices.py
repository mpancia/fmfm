#!/usr/bin/env python3
"""Render the Braids shapes on this computer and measure them.

  tools/audit_voices.py             print a table of every shape at a few timbre/colour settings
  tools/audit_voices.py --json F    write the measurements to F (used by tools/gen_presets.py)
  tools/audit_voices.py --check     test every factory sound in voices/presets.h (make audit)
"""
import json
import subprocess
import sys
from pathlib import Path

import numpy

ROOT = Path(__file__).resolve().parent.parent
BIN = ROOT / "build/voice_render"
RATE = 44100
# shapes whose top partials fall above the Nyquist limit: silent in the top octaves, so patches keep them low
LOW_ONLY = {21, 24}
PERCUSSIVE = {28, 32, 33, 34, 35, 36, 45, 47}      # level depends on pitch by design
SETTINGS = [(t, c) for t in (4096, 16384, 28672) for c in (4096, 16384, 28672)]


def build():
    BIN.parent.mkdir(exist_ok=True)
    sources = [ROOT / "tests/voice_render.cc", ROOT / "voices/voice.cc", ROOT / "voices/stmlib/utils/random.cc",
               *sorted((ROOT / "voices/braids").glob("*.cc"))]
    newest = max(p.stat().st_mtime for p in sources)
    if BIN.exists() and BIN.stat().st_mtime > newest:
        return
    subprocess.run(["g++", "-O2", "-std=c++11", "-DTEST", "-w", "-I", str(ROOT / "voices"), "-o", str(BIN),
                    *map(str, sources)], check=True)


def render(shape, timbre, color, note, seconds=1.0):
    run = subprocess.run([str(BIN), str(shape), str(timbre), str(color), str(note), str(seconds)],
                         capture_output=True, check=True)
    return numpy.frombuffer(run.stdout, dtype=numpy.int16).astype(float), float(run.stderr)


def measure(shape, timbre, color, note=60):
    x, ns = render(shape, timbre, color, note)
    body = x[RATE // 10:]
    spectrum = numpy.abs(numpy.fft.rfft(body * numpy.hanning(len(body)))) + 1e-9
    freqs = numpy.fft.rfftfreq(len(body), 1 / RATE)
    first, last = x[: RATE // 3], x[-RATE // 3:]
    return {
        "shape": shape, "timbre": timbre, "color": color, "note": note,
        "peak": float(numpy.abs(x).max()), "rms": float(body.std()),
        "clip": float(numpy.mean(numpy.abs(x) >= 32760)),
        "centroid": float((spectrum * freqs).sum() / spectrum.sum()),
        "decay": float(last.std() / max(first.std(), 1.0)),
        "ns": ns,
    }


def all_measurements():
    build()
    return [measure(s, t, c) for s in range(48) for t, c in SETTINGS]


def notes_for(shape):
    return (36, 48, 60) if shape in LOW_ONLY else (36, 60, 84)


def sound_problems(name, shape, timbre, color, gain):
    """Why a sound should not ship: it must be audible, loud enough after its gain, and not clip, in every octave."""
    levels = []
    for note in notes_for(shape):
        x, _ = render(shape, timbre, color, note, 1.0)
        x = x * gain / 256.0
        window = x[: RATE // 3] if x[-RATE // 3:].std() < 0.3 * max(x[: RATE // 3].std(), 1) else x[RATE // 10:]
        levels.append((window.std(), numpy.abs(x).max()))
    rms = [l[0] for l in levels]
    bad = []
    if max(l[1] for l in levels) > 32767:
        bad.append(f"{name}: clips ({max(l[1] for l in levels):.0f})")
    if min(rms) < 600:
        bad.append(f"{name}: nearly silent at note {notes_for(shape)[rms.index(min(rms))]} (rms {min(rms):.0f})")
    elif shape not in PERCUSSIVE and max(rms) > 5 * min(rms) and min(rms) < 2500:
        bad.append(f"{name}: level swings between notes (rms {min(rms):.0f} to {max(rms):.0f})")
    return bad


def check_sounds():
    import re
    text = (ROOT / "voices/presets.h").read_text()
    rows = re.findall(r'\{"([^"]+)", (\d+), (\d+), (\d+), (\d+), (\d+), (\d+), (\d+)\}', text.split("NPATCHES")[0])
    build()
    bad = []
    for name, shape, _attack, _release, _env, timbre, color, gain in rows:
        bad += sound_problems(name, int(shape), int(timbre), int(color), int(gain))
    print(f"audit: {len(rows)} sounds, {len(bad)} problems")
    for line in bad:
        print("  " + line)
    return 1 if bad else 0


if __name__ == "__main__":
    if "--check" in sys.argv:
        sys.exit(check_sounds())
    rows = all_measurements()
    if len(sys.argv) > 2 and sys.argv[1] == "--json":
        Path(sys.argv[2]).write_text(json.dumps(rows))
    else:
        for r in rows:
            print(f"{r['shape']:2d} t{r['timbre']:5d} c{r['color']:5d} peak {r['peak']:6.0f} rms {r['rms']:6.0f} "
                  f"centroid {r['centroid']:6.0f} decay {r['decay']:5.2f} ns {r['ns']:5.1f}")
