#!/usr/bin/env python3
"""Rewrite the sample-rate dependent tables in voices/braids/resources.cc.

Braids was built for 96 kHz. The pitch, resonator and filter tables depend on the sample rate; this script
recomputes them (same formulas as braids/resources/lookup_tables.py, Emilie Gillet, MIT) for ours.

  tools/braids_tables.py --rate 44100 --write     rewrite voices/braids/resources.cc in place
  tools/braids_tables.py --rate 96000 --check     confirm the formulas reproduce the file's current tables
"""
import argparse
import re
import sys
from pathlib import Path

import numpy

TARGET = Path(__file__).resolve().parent.parent / "voices/braids/resources.cc"


def tables(rate):
    excursion = 65536 * 65536.0
    notes = numpy.arange(128 * 128.0, (128 + 12) * 128.0 + 16, 16)
    pitches = 440.0 * 2 ** ((notes - 69 * 128) / (128 * 12))
    out = {
        "lut_oscillator_increments": (excursion / rate * pitches).astype(int),
        "lut_oscillator_delays": (rate / pitches * 65536 * 4096).astype(int),
    }

    cutoff = 440.0 * 2 ** ((numpy.arange(0, 129) - 69) / 12.0)
    f = cutoff / (rate / 2)
    f[f > 0.25] = 0.25
    gains = []
    for fi in f:
        n = numpy.arange(2000)
        response = numpy.sin((n + 1) * 2 * numpy.pi * fi) / numpy.sin(2 * numpy.pi * fi)
        response *= 0.99985 ** n
        response /= (2 * fi) ** 0.5
        gains.append(numpy.abs(response).max())
    gains = numpy.maximum(1, numpy.minimum(256, 16384.0 / numpy.array(gains)))
    out["lut_resonator_coefficient"] = (2 * numpy.cos(2 * numpy.pi * f) * 32768.0).astype(int)
    out["lut_resonator_scale"] = gains.astype(int)

    cutoff = 440.0 * 2 ** ((numpy.arange(0, 257) - 69) / 12.0)
    f = cutoff / rate
    f[f > 1 / 8.0] = 1 / 8.0
    f = 2 * numpy.sin(numpy.pi * f)
    resonance = numpy.arange(0, 257) / 260.0
    damp = numpy.minimum(2 * (1 - resonance ** 0.25), numpy.minimum(2, 2 / f - f * 0.5))
    out["lut_svf_cutoff"] = (f * 32767.0).astype(int)
    out["lut_svf_damp"] = (damp * 32767.0).astype(int)
    out["lut_svf_scale"] = (((damp / 2) ** 0.5) * 32767.0).astype(int)
    return out


def array_pattern(name):
    return re.compile(r"(const \w+ " + name + r"\[\] = \{\n)(.*?)(\n\};)", re.S)


def body(values):
    lines = [", ".join(str(int(v)) for v in values[i:i + 4]) for i in range(0, len(values), 4)]
    return "  " + ",\n  ".join(lines)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rate", type=int, required=True)
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    text = TARGET.read_text()
    bad = []
    for name, values in tables(args.rate).items():
        m = array_pattern(name).search(text)
        if not m:
            sys.exit(f"{name} not found in {TARGET}")
        if args.check:
            have = [int(x) for x in re.findall(r"-?\d+", m.group(2))]
            if have != [int(v) for v in values]:
                bad.append(name)
        else:
            text = text[:m.start(2)] + body(values) + text[m.end(2):]
    if args.check:
        print("mismatch: " + ", ".join(bad) if bad else "tables match")
        sys.exit(1 if bad else 0)
    if args.write:
        TARGET.write_text(text)
        print(f"wrote {TARGET} for {args.rate} Hz")


if __name__ == "__main__":
    main()
