#!/usr/bin/env python3
"""Generate voices/presets.h: the factory sounds and patches.

Sounds come from measurements (tools/audit_voices.py): for each Braids shape the settings that sound most
different are kept (ordered dark to bright), each with a gain that brings it to a common loudness. Patches are
the hand-written table below, naming sounds as "SHAPE WORD".

  tools/gen_presets.py --write     rewrite voices/presets.h and Spec/Presets.lean (the same patches as Lean data,
                                   so Proofs/Presets.lean can check that every one fits the knob ranges)
  tools/gen_presets.py --check     fail if either is out of date (make lint runs this)
"""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import audit_voices  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
TARGET = ROOT / "voices/presets.h"
LEAN_TARGET = ROOT / "Spec/Presets.lean"
NAMES = ["CSAW", "MORPH", "SAW SQR", "SIN TRI", "BUZZ", "SQR SUB", "SAW SUB", "SQR SYNC", "SAW SYNC", "3 SAW",
         "3 SQR", "3 TRI", "3 SIN", "3 RING", "SWARM", "SAW COMB", "TOY", "FLT LP", "FLT PK", "FLT BP", "FLT HP",
         "VOSIM", "VOWEL", "VOWEL F", "HARMONIC", "FM", "FBK FM", "CHAOS FM", "PLUCK", "BOW", "BLOW", "FLUTE",
         "BELL", "DRUM", "KICK", "CYMBAL", "SNARE", "WAVETBL", "WAVE MAP", "WAVE LN", "WAVE PARA", "NOISE FLT",
         "TWIN PK", "CLK NOISE", "GRANULAR", "PARTICLE", "DIGI MOD", "?",
         "FM PIANO", "FM BELL", "FM BASS", "FM BRASS", "FM GLASS", "FM MALLET", "FM ORGAN", "FM CLANG"]   # 48 on: Firmware/Fm.lean
SHAPE = {n: i for i, n in enumerate(NAMES)}
PERCUSSIVE = {"BELL", "DRUM", "KICK", "CYMBAL", "SNARE", "PARTICLE", "?", "PLUCK", "FM PIANO", "FM BELL", "FM MALLET",
              "FM CLANG"}
RINGING = {"PLUCK", "BELL", "DRUM", "FM PIANO", "FM BELL", "FM MALLET", "FM CLANG"}   # the long release class
TARGET_RMS, PEAK_LIMIT = 9000.0, 30000.0

# attack class 0..3 and release class 0..6 index the tables in dinghy.c (about 2/8/30/90 ms; 10 ms to 1.8 s)
PAD_SHAPES = ["3 SAW", "SWARM", "VOWEL", "3 SIN", "WAVE MAP", "GRANULAR", "SAW COMB", "FLT LP", "HARMONIC",
              "BLOW", "BOW", "TWIN PK", "FM GLASS", "FM ORGAN", "FM BRASS"]
PLUCK_SHAPES = ["CSAW", "MORPH", "SQR SUB", "SAW SUB", "3 SQR", "FM", "FBK FM", "CHAOS FM", "FLT LP", "WAVETBL",
                "VOSIM", "DIGI MOD", "BUZZ", "FM BASS"]
WORDS = {5: ["DARK", "WARM", "MID", "BRIGHT", "SHARP"], 4: ["DARK", "MID", "BRIGHT", "SHARP"],
         3: ["DARK", "MID", "BRIGHT"], 2: ["DARK", "BRIGHT"], 1: ["MID"]}


def pick(rows):
    """up to five usable settings of one shape that sound clearly different, dark to bright"""
    ok = [r for r in rows if r["rms"] > 300 or r["peak"] > 3000]
    ok.sort(key=lambda r: r["centroid"])
    unique = []
    for r in ok:
        if not unique or r["centroid"] - unique[-1]["centroid"] > 0.12 * max(unique[-1]["centroid"], 1):
            unique.append(r)
    while len(unique) > 5:                      # keep the five most evenly spread
        gaps = [unique[i + 1]["centroid"] - unique[i - 1]["centroid"] for i in range(1, len(unique) - 1)]
        del unique[1 + gaps.index(min(gaps))]
    return unique


def gain_q8(r):
    """gain that brings the sound to a common loudness at the middle note without clipping at any note"""
    level = r["rms"] if r["decay"] > 0.3 else max(r["rms"] * 2.5, r["peak"] * 0.15)
    peak = max(audit_voices.measure(r["shape"], r["timbre"], r["color"], n)["peak"]
               for n in audit_voices.notes_for(r["shape"]))
    gain = min(TARGET_RMS / max(level, 1), PEAK_LIMIT / max(peak, 1), 8.0)
    return max(int(gain * 256), 32)


def sounds(measurements):
    by_shape = {}
    for r in measurements:
        by_shape.setdefault(r["shape"], []).append(r)
    out = []

    def add(shape, word, r, attack, release, env):
        kind = (1 if word == "PLUCK" or NAMES[shape] in ("PLUCK", "FM PIANO", "FM MALLET") else 2 if word == "PAD"
                else 3 if NAMES[shape] in PERCUSSIVE else 0)                    # the sound's type: tone, pluck, pad, drum
        out.append({"name": f"{NAMES[shape]} {word}", "shape": shape, "type": kind, "timbre": r["timbre"],
                    "color": r["color"], "attack": attack, "release": release, "env": env, "gain": gain_q8(r)})

    def add_checked(shape, word, r, attack, release, env):
        before = len(out)
        add(shape, word, r, attack, release, env)
        s = out[-1]
        if audit_voices.sound_problems(s["name"], s["shape"], s["timbre"], s["color"], s["gain"]):
            del out[before:]                    # a sound that fails the audit is not shipped

    for shape in range(len(NAMES)):
        name = NAMES[shape]
        chosen = pick(by_shape[shape])
        if not chosen:
            continue
        for r, word in zip(chosen, WORDS[len(chosen)]):
            if name in PERCUSSIVE:
                add_checked(shape, word, r, 0, 5 if name in RINGING else 4, 0)
            else:
                add_checked(shape, word, r, 1, 2, 0)
        mid = chosen[len(chosen) // 2] if chosen else None
        if mid and name in PAD_SHAPES:
            add_checked(shape, "PAD", mid, 3, 5, 0)
        if mid and name in PLUCK_SHAPES:
            add_checked(shape, "PLUCK", mid, 0, 2, 10)
    return out


# One row per patch: name, bpm, key (semitones above C), then four lanes of
# (hits, steps, speed index, scale index, sound, lowest note, note span, seed[, extras[, feel]]).
# speed index into [1/48 1/32 1/24 1/16 1/12 1/8 1/6 1/4]; scale index into
# [MAJOR MINOR PENT+ PENT- DORIAN H.MIN WHOLE CHROM PHRYG LYDIAN BLUES UKR.D DBL.H H.MAJ].
PATCHES = [
    ("VELVET MIST", 76, 0, [(3, 8, 5, 2, "3 SIN PAD", 48, 12, 1), (5, 16, 3, 2, "FLUTE MID", 60, 24, 2),
                            (2, 8, 5, 4, "VOWEL PAD", 55, 12, 3), (1, 4, 7, 2, "BELL MID", 72, 12, 4)]),
    ("SLOW DRIFT", 60, 2, [(2, 8, 6, 3, "SWARM PAD", 36, 12, 5), (3, 8, 5, 3, "BOW MID", 48, 12, 6),
                           (5, 16, 4, 3, "FLUTE BRIGHT", 60, 24, 7), (1, 8, 6, 3, "GRANULAR PAD", 72, 12, 8)]),
    ("PAPER LANTERNS", 92, 0, [(4, 8, 5, 2, "PLUCK MID", 48, 12, 9), (7, 16, 3, 2, "BELL BRIGHT", 72, 12, 10),
                               (5, 12, 4, 2, "FM PLUCK", 60, 24, 11), (3, 8, 5, 2, "WAVETBL PLUCK", 55, 12, 12)]),
    ("TIDEPOOL", 84, 4, [(3, 8, 5, 10, "FBK FM PLUCK", 48, 12, 13), (5, 16, 3, 10, "FM MID", 60, 24, 14),
                         (2, 8, 6, 10, "CHAOS FM DARK", 36, 12, 15), (7, 16, 3, 10, "BELL DARK", 72, 12, 16)]),
    ("NEON RAIN", 118, 5, [(4, 16, 3, 4, "SAW SUB PLUCK", 36, 12, 17), (9, 16, 3, 4, "CSAW PLUCK", 60, 24, 18),
                           (5, 16, 3, 4, "3 SQR PLUCK", 48, 12, 19), (3, 8, 4, 4, "FM BRIGHT", 72, 12, 20)]),
    ("CONCRETE GARDEN", 124, 0, [(4, 16, 3, 7, "KICK MID", 36, 1, 21), (5, 16, 3, 7, "SNARE MID", 40, 1, 22),
                                 (9, 16, 3, 7, "CYMBAL MID", 60, 1, 23), (5, 16, 3, 1, "SQR SUB PLUCK", 36, 12, 24)]),
    ("MARBLE HALLS", 70, 7, [(3, 8, 5, 5, "3 SAW PAD", 48, 12, 25), (5, 8, 4, 5, "VOSIM PLUCK", 36, 12, 26),
                             (2, 8, 6, 5, "VOWEL F MID", 55, 12, 27), (3, 16, 3, 5, "BELL MID", 72, 12, 28)]),
    ("GLASS ORCHARD", 80, 9, [(3, 8, 5, 9, "HARMONIC MID", 48, 12, 29), (7, 16, 3, 9, "FLUTE DARK", 60, 24, 30),
                              (5, 8, 5, 9, "PLUCK BRIGHT", 55, 12, 31), (2, 8, 6, 9, "WAVE MAP PAD", 72, 12, 32)]),
    ("DEEP FIELD", 54, 3, [(1, 4, 7, 1, "SAW SUB DARK", 24, 12, 33), (2, 8, 6, 1, "BOW DARK", 36, 12, 34),
                           (3, 8, 6, 1, "3 SIN PAD", 48, 24, 35), (1, 8, 7, 1, "BELL DARK", 60, 12, 36)]),
    ("BROKEN CLOCK", 132, 0, [(5, 8, 2, 6, "TOY MID", 48, 12, 37), (7, 12, 3, 6, "CLK NOISE MID", 60, 12, 38),
                              (3, 8, 3, 6, "BUZZ PLUCK", 36, 12, 39), (4, 16, 2, 6, "DIGI MOD PLUCK", 72, 12, 40)]),
    ("SALT AND IRON", 100, 2, [(4, 16, 3, 8, "KICK BRIGHT", 36, 1, 41), (3, 8, 4, 8, "DRUM MID", 43, 1, 42),
                               (5, 16, 3, 8, "SAW SYNC MID", 48, 12, 43), (7, 16, 3, 8, "NOISE FLT MID", 72, 12, 44)]),
    ("SUNDAY MORNING", 88, 7, [(3, 8, 5, 0, "FLUTE MID", 60, 12, 45), (5, 16, 4, 0, "PLUCK MID", 48, 12, 46),
                               (2, 8, 6, 0, "3 TRI MID", 36, 12, 47), (4, 8, 5, 0, "BELL BRIGHT", 72, 12, 48)]),
    ("THE LONG WAY", 66, 5, [(5, 16, 4, 1, "MORPH PLUCK", 48, 12, 49), (3, 16, 3, 1, "BLOW MID", 60, 12, 50),
                             (2, 8, 6, 1, "SWARM PAD", 36, 12, 51), (1, 4, 7, 1, "VOWEL PAD", 72, 12, 52)]),
    ("COPPER WIRE", 110, 0, [(6, 16, 3, 3, "SAW COMB PAD", 36, 12, 53), (11, 16, 3, 3, "FLT BP MID", 60, 24, 54),
                             (5, 16, 3, 3, "WAVE LN MID", 48, 12, 55), (3, 8, 4, 3, "FBK FM BRIGHT", 72, 12, 56)]),
    ("LITTLE ORBITS", 96, 0, [(3, 8, 3, 2, "PLUCK DARK", 60, 12, 57), (5, 8, 4, 2, "PLUCK MID", 67, 12, 58),
                              (7, 8, 5, 2, "PLUCK BRIGHT", 72, 12, 59), (3, 16, 6, 2, "BELL MID", 48, 12, 60)]),
    ("TAPE HISS DREAM", 72, 10, [(2, 8, 5, 2, "GRANULAR MID", 48, 24, 61), (3, 8, 6, 2, "NOISE FLT DARK", 60, 12, 62),
                                 (1, 4, 7, 2, "PARTICLE MID", 72, 12, 63), (2, 8, 6, 2, "TWIN PK PAD", 36, 12, 64)]),
    ("CATHEDRAL", 58, 0, [(2, 8, 6, 5, "VOWEL PAD", 48, 12, 65), (3, 8, 6, 5, "VOWEL F MID", 55, 12, 66),
                          (2, 8, 7, 5, "3 SAW PAD", 36, 12, 67), (1, 8, 7, 5, "BELL DARK", 72, 12, 68)]),
    ("PIXEL FOREST", 140, 7, [(5, 16, 3, 2, "SQR SYNC PLUCK", 60, 12, 69), (9, 16, 3, 2, "SAW SYNC MID", 48, 12, 70),
                              (3, 8, 3, 2, "TOY BRIGHT", 72, 12, 71), (4, 16, 3, 2, "SQR SUB PLUCK", 36, 12, 72)]),
    ("HARBOUR LIGHTS", 90, 3, [(3, 8, 5, 4, "3 SIN PAD", 48, 12, 73), (5, 16, 3, 4, "FM PLUCK", 60, 24, 74),
                               (2, 8, 6, 4, "WAVE PARA MID", 55, 12, 75), (3, 8, 4, 4, "BELL BRIGHT", 72, 12, 76)]),
    ("FERRO", 104, 0, [(7, 16, 3, 12, "CHAOS FM PLUCK", 48, 12, 77), (5, 16, 3, 12, "FBK FM BRIGHT", 60, 12, 78),
                       (3, 8, 4, 12, "BUZZ DARK", 36, 12, 79), (9, 16, 2, 12, "CYMBAL DARK", 60, 1, 80)]),
    ("MOSS AND STONE", 78, 5, [(3, 8, 5, 3, "DRUM DARK", 40, 1, 81), (4, 8, 5, 3, "BOW MID", 48, 12, 82),
                               (5, 16, 3, 3, "FLUTE MID", 60, 24, 83), (2, 8, 6, 3, "BELL DARK", 72, 12, 84)]),
    ("CIRCUIT BLOOM", 126, 9, [(5, 16, 3, 5, "FLT LP PLUCK", 36, 12, 85), (7, 16, 3, 5, "FLT PK MID", 60, 24, 86),
                               (5, 16, 4, 5, "WAVETBL MID", 48, 12, 87), (3, 8, 3, 5, "FM BRIGHT", 72, 12, 88)]),
    ("ICE HARP", 82, 2, [(5, 8, 5, 2, "PLUCK BRIGHT", 60, 24, 89), (3, 8, 5, 2, "BELL BRIGHT", 72, 12, 90),
                         (2, 8, 6, 2, "HARMONIC PAD", 48, 12, 91), (1, 4, 7, 2, "3 SIN PAD", 36, 12, 92)]),
    ("LAST TRAIN", 112, 0, [(4, 16, 3, 10, "KICK DARK", 36, 1, 93), (5, 16, 3, 10, "SNARE DARK", 40, 1, 94),
                            (3, 16, 3, 10, "SAW SUB PLUCK", 36, 12, 95), (7, 16, 3, 10, "FLT BP MID", 60, 24, 96)]),
    ("WARM STATIC", 64, 0, [(2, 8, 6, 0, "3 TRI PAD", 48, 12, 97), (3, 8, 5, 0, "FLUTE DARK", 60, 12, 98),
                            (1, 8, 7, 0, "NOISE FLT MID", 72, 12, 99), (2, 4, 7, 0, "BOW DARK", 36, 12, 100)]),
]
# Sounds by the job they do in a patch. The patch recipes below draw from these.
ROLE_SOUNDS = {
    "bass": ["SAW SUB DARK", "SAW SUB PLUCK", "SQR SUB MID", "SQR SUB PLUCK", "CSAW DARK", "3 SQR DARK", "FM DARK",
             "FBK FM DARK", "FLT LP DARK", "BUZZ DARK", "MORPH DARK", "SAW COMB DARK", "BOW DARK"],
    "pad": ["3 SAW PAD", "SWARM PAD", "3 SIN PAD", "VOWEL PAD", "GRANULAR PAD", "WAVE MAP PAD", "HARMONIC PAD",
            "BOW PAD", "BLOW PAD", "TWIN PK PAD", "FLT LP PAD", "SAW COMB PAD", "3 SAW MID", "3 TRI MID"],
    "lead": ["FM PLUCK", "FM MID", "FM BRIGHT", "FBK FM MID", "FBK FM BRIGHT", "FLUTE MID", "FLUTE BRIGHT",
             "CSAW PLUCK", "WAVETBL PLUCK", "VOSIM PLUCK", "3 TRI MID", "SIN TRI BRIGHT", "SAW SQR BRIGHT",
             "MORPH PLUCK", "PLUCK MID", "PLUCK BRIGHT", "VOWEL F MID", "WAVE LN MID", "CHAOS FM PLUCK",
             "DIGI MOD PLUCK", "FLT PK MID", "FLT BP MID", "HARMONIC MID"],
    "bell": ["BELL DARK", "BELL MID", "BELL BRIGHT", "PARTICLE MID", "NOISE FLT DARK", "NOISE FLT MID",
             "TOY MID", "DRUM MID", "WAVE PARA MID", "GRANULAR MID", "CLK NOISE MID", "? MID", "TWIN PK MID"],
    "kick": ["KICK DARK", "KICK MID", "KICK BRIGHT"],
    "snare": ["SNARE DARK", "SNARE MID", "SNARE BRIGHT", "DRUM MID"],
    "hat": ["CYMBAL DARK", "CYMBAL MID", "CYMBAL BRIGHT", "NOISE FLT BRIGHT"],
}
# A mood: scales to pick from, tempo range, then one line per lane: role, hit counts, step counts, speeds
# (indexes into the speed list), lowest note and span.
MOODS = [
    ("calm", [0, 2, 9, 1], (56, 84), [("pad", [2, 3], [8], [5, 6], 48, 12), ("lead", [3, 5], [8, 16], [4, 5], 60, 24),
                                      ("pad", [2, 3], [8], [6], 55, 12), ("bell", [1, 2, 3], [4, 8], [6, 7], 72, 12)]),
    ("dream", [2, 3, 4, 9], (66, 96), [("bass", [2, 3], [8], [5, 6], 36, 12), ("pad", [3, 5], [8, 12], [4, 5], 48, 12),
                                       ("lead", [3, 5, 7], [8, 16], [3, 4], 60, 24), ("bell", [2, 3], [8], [5, 6], 72, 12)]),
    ("drive", [1, 5, 10, 11], (104, 132), [("bass", [4, 5, 7], [16], [3], 36, 12), ("lead", [5, 7, 9], [16], [3], 60, 24),
                                           ("lead", [3, 5], [8, 12], [3, 4], 48, 12), ("bell", [3, 5], [8, 16], [3, 4], 72, 12)]),
    ("pulse", [1, 4, 8, 12], (112, 138), [("kick", [4, 5], [16], [3], 36, 1), ("snare", [2, 3, 5], [16], [3], 40, 1),
                                          ("hat", [7, 9, 11], [16], [2, 3], 60, 1), ("bass", [5, 7], [16], [3], 36, 12)]),
    ("drift", [3, 2, 0, 9], (48, 70), [("bass", [1, 2], [4, 8], [6, 7], 24, 12), ("pad", [2, 3], [8], [6, 7], 36, 24),
                                       ("pad", [3, 5], [8, 16], [5, 6], 55, 12), ("bell", [1, 2], [4, 8], [7], 60, 12)]),
    ("shimmer", [9, 0, 2, 13], (72, 100), [("lead", [3, 5, 7], [8, 16], [4, 5], 60, 24), ("bell", [3, 5], [8], [5], 72, 12),
                                           ("pad", [2, 3], [8], [6], 48, 12), ("lead", [4, 5], [12, 16], [3, 4], 55, 12)]),
    ("machine", [6, 7, 10, 12], (120, 146), [("bass", [5, 7, 9], [16], [2, 3], 36, 12), ("lead", [7, 9, 11], [12, 16], [2, 3], 48, 12),
                                             ("bell", [3, 5, 7], [8, 16], [2, 3], 72, 12), ("hat", [9, 11], [16], [2], 60, 1)]),
    ("folk", [0, 2, 4, 1], (80, 108), [("lead", [3, 5], [8], [4, 5], 55, 12), ("lead", [4, 5, 7], [8, 16], [3, 4], 60, 12),
                                       ("bass", [2, 3], [8], [5], 36, 12), ("bell", [2, 3], [8], [5, 6], 72, 12)]),
]
ADJECTIVES = ["VELVET", "PAPER", "COPPER", "SALT", "GLASS", "MOSS", "NEON", "TIDAL", "AMBER", "QUIET", "SLOW", "HOLLOW",
              "WILD", "SOFT", "LUNAR", "RUSTED", "PALE", "ELECTRIC", "HIDDEN", "FAINT", "BRIGHT", "WINTER", "SMALL", "LOST"]
NOUNS = ["MIST", "GARDEN", "ORBIT", "HARBOUR", "LANTERN", "ENGINE", "FOREST", "ECHO", "DESERT", "SIGNAL", "RIVER",
         "CLOCK", "ISLAND", "WINDOW", "COMET", "FIELD", "BRIDGE", "STATION", "CANYON", "MEADOW", "TOWER", "VALLEY"]


def longest_shape(name):
    return max((n for n in NAMES if name.startswith(n + " ")), key=len)


# hand patches: note algorithm, chance, amount, mutate, chord follow, level, by lane position
HAND_EXTRAS = [(1, 100, 2, 10, 0, 100, 15), (5, 100, 8, 15, 0, 100, 35), (5, 100, 16, 8, 0, 100, 30), (0, 85, 4, 10, 0, 100, 45)]
# by role: choices of (algo, chance, amount, mutate, chord)
ROLE_EXTRAS = {
    "bass": [(1, 100, 2, 10, 0), (2, 100, 4, 10, 0), (3, 100, 4, 10, 0), (4, 100, 4, 10, 0), (0, 90, 4, 10, 0)],
    "pad": [(1, 100, 1, 10, 0), (1, 90, 2, 10, 0), (5, 100, 4, 5, 0), (4, 100, 3, 10, 0)],
    "lead": [(5, 100, 8, 10, 0), (5, 100, 16, 6, 0), (5, 100, 4, 20, 0), (1, 100, 3, 10, 0), (0, 85, 4, 10, 0)],
    "bell": [(0, 80, 4, 10, 0), (4, 100, 4, 10, 0), (0, 100, 4, 10, 0), (1, 70, 2, 10, 0)],
    "kick": [(0, 100, 1, 0, 0)], "snare": [(0, 100, 1, 0, 0)], "hat": [(0, 85, 1, 0, 0), (0, 100, 1, 0, 0)],
}
# chord progressions (scale degrees, one chord per bar or more): index into Harmony.degree in Firmware/Harmony.lean
# reverb send by role, in percent
ROLE_SEND = {"bass": 8, "pad": 45, "lead": 28, "bell": 50, "kick": 5, "snare": 15, "hat": 12}
# pan by role (0 left, 50 middle, 100 right): the low things stay in the middle, the rest spread a little
HAND_PANS = (50, 40, 62, 50)                   # the hand-written patches: bass middle, lead a little left, bell right, pad middle
ROLE_PAN = {"bass": 50, "pad": 50, "lead": 40, "bell": 62, "kick": 50, "snare": 45, "hat": 60}
# reverb decay, brightness and return by mood
MOOD_REVERB = {"calm": (75, 55, 75), "dream": (80, 50, 80), "drive": (35, 65, 55), "pulse": (30, 70, 50), "drift": (90, 45, 85),
               "shimmer": (70, 80, 80), "machine": (30, 75, 50), "folk": (55, 60, 65)}
# delay note value (0 1/32 .. 7 1/4: 2 is 1/8 triplet, 6 a dotted 1/8), feedback, tone and return by mood
MOOD_DELAY = {"calm": (6, 35, 50, 30), "dream": (6, 50, 40, 45), "drive": (4, 30, 70, 25), "pulse": (1, 25, 80, 30),
              "drift": (7, 55, 35, 40), "shimmer": (6, 45, 90, 45), "machine": (1, 40, 70, 35), "folk": (4, 20, 60, 0)}
PROGRESSION_NAMES = ["OFF", "I-IV-V-I", "I-V-vi-IV", "vi-IV-I-V", "ii-V-I-I", "i-VI-III-VII", "I-iii-IV-V", "I-vi-ii-V"]
MOOD_PROGRESSIONS = {"calm": [2, 3, 6], "dream": [3, 2, 0], "drive": [5, 7, 0], "pulse": [0], "drift": [0, 4],
                     "shimmer": [2, 3, 6], "machine": [0], "folk": [1, 2, 6]}


def generated_patches(count):
    import random
    rng = random.Random(20261031)
    names = set(p[0] for p in PATCHES)
    out = []
    while len(out) < count:
        mood = MOODS[len(out) % len(MOODS)]
        name = f"{rng.choice(ADJECTIVES)} {rng.choice(NOUNS)}"
        if name in names:
            continue
        names.add(name)
        mood_name, scales, (lo, hi), lanes = mood
        scale = rng.choice(scales)
        progression = rng.choice(MOOD_PROGRESSIONS[mood_name])
        rate = rng.choice([1, 2])
        cells = []
        for role, hits, steps, speeds, low, span in lanes:
            st = rng.choice(steps)
            sound = rng.choice(ROLE_SOUNDS[role])
            while SHAPE[longest_shape(sound)] in audit_voices.LOW_ONLY and low + span > 72:
                sound = rng.choice(ROLE_SOUNDS[role])       # these shapes go silent in the top octaves
            algo, chance, amount, mutate, _ = rng.choice(ROLE_EXTRAS[role])
            chord = (2 if role == "bass" else 1 if role == "pad" else 0) if progression else 0
            cells.append((min(rng.choice(hits), st), st, rng.choice(speeds), scale if role not in ("kick", "snare", "hat") else 7,
                          sound, low, span, rng.randrange(1, 1000), (algo, chance, amount, mutate, chord, 100, ROLE_SEND[role]),
                          (0, 0, 0, 90, 1, 1), ROLE_PAN[role]))
        out.append((name, rng.randrange(lo, hi + 1), rng.randrange(12), cells, progression, rate, MOOD_REVERB[mood_name],
                    MOOD_DELAY[mood_name]))
    return out


# The demo songs: each shows the sequencers off (docs/SEQUENCERS.md). A lane is (hits, steps, speed, scale, sound,
# low, span, seed, (algo, chance, amount, mutate, chord, level, send), (feel, rotate, accents, rule, ratchet, sub-hits)).
# Algorithms: 0 random 1 walk 2 up 3 down 4 bounce 5 loop 6 turing 7 step 8 markov 9 grammar 10 chord.
# Feel: 0 euclid 1 rotate 2 automaton 3 ratchet. The first demo is the boot patch.
EUCLID = (0, 0, 0, 90, 1, 1)
DEMOS = [
    # a clockwork groove: a locked turing bass, a rule-30 automaton ticking on a dark string, ratcheted stabs, a markov bell
    ("CLOCKWORK", 104, 2, [(4, 16, 3, 4, "SAW SUB DARK", 36, 12, 201, (6, 100, 8, 0, 2, 100, 10), (1, 0, 2, 90, 1, 1)),
                           (6, 16, 3, 4, "PLUCK DARK", 55, 12, 202, (2, 100, 1, 0, 1, 65, 40), (2, 0, 0, 30, 1, 1)),
                           (3, 8, 5, 4, "MORPH PLUCK", 60, 12, 203, (8, 100, 1, 15, 1, 80, 35), (3, 0, 0, 90, 3, 2)),
                           (5, 12, 5, 4, "BELL DARK", 72, 12, 204, (1, 70, 2, 0, 1, 55, 65), (1, 3, 2, 90, 1, 1))],
     2, 2, (70, 50, 65), (4, 40, 55, 35)),
    # after Eno's Music for Airports: bars of 7, 11, 13 and 5 steps (pairwise coprime, so they realign only every
    # 5005 steps), sparse, D pentatonic over a slow I-V-vi-IV, a long reverb
    ("AIRPORTS", 64, 2, [(1, 7, 7, 2, "3 SIN PAD", 36, 12, 101, (10, 100, 2, 0, 2, 100, 40)),
                         (3, 11, 5, 2, "FLUTE MID", 60, 12, 102, (6, 100, 5, 0, 1, 100, 50), (1, 2, 1, 90, 1, 1)),
                         (2, 13, 5, 2, "BELL DARK", 72, 12, 103, (8, 100, 1, 10, 1, 95, 60)),
                         (1, 5, 7, 2, "GRANULAR PAD", 48, 7, 104, (9, 60, 1, 50, 1, 90, 55))],
     2, 4, (90, 45, 80), (7, 50, 40, 35)),
    # after Reich: two plucks on the same locked phrase, one on 12 steps and one on 13, drifting apart and back
    ("PHASES", 120, 7, [(12, 12, 3, 2, "PLUCK MID", 60, 12, 301, (6, 100, 12, 0, 0, 90, 25)),
                        (13, 13, 3, 2, "PLUCK BRIGHT", 60, 12, 301, (6, 100, 12, 0, 0, 90, 25)),
                        (1, 8, 7, 2, "SAW SUB DARK", 36, 7, 303, (2, 100, 1, 0, 0, 100, 10)),
                        (2, 16, 5, 2, "BELL BRIGHT", 72, 12, 304, (0, 40, 1, 0, 0, 60, 60))],
     0, 1, (50, 65, 55), (3, 30, 70, 25)),
    # cellular automata: rule 90 draws its triangle on 32 steps, rule 110 crawls on 16, rule 30 boils underneath
    ("SIERPINSKI", 96, 9, [(1, 32, 3, 9, "BELL MID", 72, 12, 401, (2, 100, 1, 0, 1, 90, 55), (2, 0, 0, 90, 1, 1)),
                           (1, 16, 5, 9, "WAVETBL PLUCK", 60, 12, 402, (4, 100, 1, 0, 1, 85, 40), (2, 0, 0, 110, 1, 1)),
                           (2, 16, 3, 9, "TOY MID", 48, 12, 403, (0, 80, 1, 0, 0, 60, 30), (2, 0, 0, 30, 1, 1)),
                           (1, 4, 7, 9, "3 SAW PAD", 36, 12, 404, (10, 100, 3, 0, 2, 100, 45))],
     6, 2, (70, 60, 65), (6, 45, 55, 40)),
    # markov melodies in each style over a walking bass; play the keys and the lanes learn from you
    ("MARKET", 96, 5, [(4, 8, 5, 4, "SQR SUB MID", 36, 12, 501, (1, 100, 2, 0, 2, 100, 10)),
                       (5, 8, 3, 4, "VOWEL MID", 60, 12, 502, (8, 90, 1, 10, 1, 90, 35)),
                       (3, 8, 5, 4, "MORPH WARM", 48, 12, 503, (8, 100, 4, 20, 1, 85, 30)),
                       (3, 16, 3, 4, "BELL BRIGHT", 72, 12, 504, (8, 60, 2, 10, 1, 70, 60))],
     5, 2, (55, 60, 60), (6, 35, 60, 30)),
    # grammars: a fibonacci line, a thue-morse line and a round, in lydian, with the first lane holding the chord
    ("FIBONACCI", 80, 0, [(1, 4, 7, 9, "3 SIN PAD", 36, 12, 601, (10, 100, 3, 0, 2, 60, 40)),
                          (5, 8, 5, 9, "FLUTE MID", 60, 12, 602, (9, 100, 1, 75, 1, 55, 45)),
                          (5, 8, 5, 9, "BOW MID", 48, 12, 603, (9, 100, 3, 50, 1, 50, 40)),
                          (3, 8, 3, 9, "PLUCK BRIGHT", 72, 12, 604, (9, 80, 4, 100, 1, 45, 50))],
     6, 2, (75, 55, 50), (6, 40, 50, 25)),
    # ratchets: a four-on-the-floor kick, a rolling snare, hats that stutter, a bass that doubles up
    ("RATCHETS", 128, 0, [(4, 16, 3, 7, "KICK MID", 36, 1, 701, (0, 100, 1, 0, 0, 100, 5)),
                          (2, 16, 3, 7, "SNARE MID", 40, 1, 702, (0, 100, 1, 0, 0, 90, 15), (3, 0, 0, 90, 4, 3)),
                          (8, 16, 3, 7, "CYMBAL MID", 60, 1, 703, (0, 90, 1, 0, 0, 60, 12), (3, 0, 0, 90, 2, 2)),
                          (3, 8, 5, 3, "SAW SUB DARK", 36, 12, 704, (6, 100, 6, 5, 0, 100, 10), (3, 0, 0, 90, 2, 1))],
     0, 1, (30, 70, 45), (1, 25, 80, 25)),
    # the Tonnetz: WALK LR through all 24 triads, a chord a bar (Proofs/Tonnetz.lean: a Hamiltonian cycle, one note
    # changing each move); a pad holds the triad, a bass and an arpeggio climb it, a bell wanders
    ("TONNETZ", 72, 0, [(1, 4, 7, 0, "FM GLASS PAD", 48, 12, 801, (10, 100, 3, 0, 2, 80, 45), (1, 1, 0, 90, 1, 1)),
                        (2, 8, 5, 0, "FM BASS MID", 36, 12, 802, (2, 100, 1, 0, 2, 100, 10)),
                        (5, 8, 4, 0, "FM PIANO MID", 60, 12, 803, (2, 100, 1, 0, 2, 90, 35)),
                        (2, 16, 3, 0, "FM BELL MID", 72, 12, 804, (0, 60, 1, 0, 1, 70, 60))],
     8, 1, (80, 50, 70), (6, 40, 55, 30)),
    # a hexatonic cycle: WALK PL, six triads in E minor's neighbourhood, bowed and slow, two bars a chord
    ("HEXATONIC", 66, 4, [(1, 4, 7, 1, "VOWEL PAD", 48, 12, 811, (10, 100, 3, 0, 2, 90, 50)),
                          (3, 8, 5, 1, "BOW MID", 48, 12, 812, (4, 100, 1, 0, 2, 95, 40)),
                          (1, 8, 6, 1, "SAW SUB DARK", 36, 12, 813, (2, 100, 1, 0, 2, 100, 10)),
                          (3, 16, 3, 1, "BELL BRIGHT", 72, 12, 814, (0, 50, 1, 0, 2, 70, 60))],
     9, 2, (85, 45, 75), (7, 45, 50, 30)),
    # an octatonic cycle: WALK PR, eight triads, plucked and quick, a chord a bar
    ("OCTATONIC", 112, 7, [(4, 16, 3, 0, "SAW SUB DARK", 36, 12, 821, (2, 100, 1, 0, 2, 100, 10)),
                           (7, 16, 3, 0, "CSAW PLUCK", 60, 12, 822, (0, 100, 1, 0, 2, 80, 30)),
                           (5, 8, 4, 0, "FM PLUCK", 55, 12, 823, (4, 100, 1, 0, 2, 75, 35)),
                           (3, 8, 5, 0, "3 SIN PAD", 48, 12, 824, (10, 100, 3, 0, 2, 60, 45))],
     10, 1, (60, 60, 55), (3, 35, 65, 30)),
    # the white keys and the black: two lanes in C major, two on COMPL, the pentatonic it leaves out; the same
    # intervals two fewer each (harmony_complement_interval_content), and never a note in common
    ("BLACK KEYS", 88, 0, [(3, 8, 5, 0, "HARMONIC MID", 48, 12, 831, (1, 100, 2, 0, 0, 80, 35)),
                           (5, 16, 3, 0, "PLUCK BRIGHT", 60, 12, 832, (0, 100, 1, 0, 0, 70, 30)),
                           (3, 8, 5, 0, "FLUTE MID", 60, 12, 833, (1, 100, 2, 0, 3, 75, 40)),
                           (2, 8, 6, 0, "WAVE MAP PAD", 72, 12, 834, (0, 80, 1, 0, 3, 55, 55))],
     0, 1, (70, 55, 60), (6, 40, 55, 30)),
    # the FM voice: an electric piano ballad in F, I-V-vi-IV two bars a chord; piano chords, a bass on the triad,
    # a glass pad holding it, a dark bell now and then
    ("ELECTRIC", 84, 5, [(2, 8, 5, 0, "FM PIANO MID", 55, 12, 901, (10, 100, 3, 0, 1, 90, 40)),
                         (3, 8, 5, 0, "FM BASS MID", 36, 12, 902, (2, 100, 1, 0, 2, 100, 10)),
                         (1, 8, 7, 0, "FM GLASS PAD", 60, 12, 903, (10, 100, 3, 0, 2, 60, 55), (1, 1, 0, 90, 1, 1)),
                         (2, 16, 3, 0, "FM BELL DARK", 72, 12, 904, (0, 45, 1, 0, 1, 55, 65))],
     2, 2, (80, 55, 65), (6, 45, 50, 30)),
    # mallets: a gamelan of bells and mallets in D pentatonic, bars of 16, 8 and 12 steps against each other
    ("LANTERNS", 108, 2, [(7, 16, 3, 2, "FM MALLET MID", 60, 12, 911, (1, 100, 2, 0, 0, 85, 35)),
                          (3, 8, 4, 2, "FM BELL BRIGHT", 72, 12, 912, (4, 100, 1, 0, 0, 60, 60)),
                          (5, 12, 3, 2, "FM MALLET DARK", 48, 12, 913, (5, 100, 5, 15, 0, 90, 30)),
                          (2, 8, 5, 2, "FM PIANO DARK", 36, 12, 914, (2, 100, 1, 0, 0, 100, 20))],
     0, 1, (65, 65, 55), (3, 35, 65, 35)),
    # vespers: an organ holds the chord of a slow i-VI-III-VII in A minor, four bars each (its one hit turned to the
    # first step, so the chord is there from the start); brass answers mid-bar, glass walks a line, a bell marks the bar
    ("VESPERS", 60, 9, [(1, 4, 7, 1, "FM ORGAN PAD", 48, 12, 921, (10, 100, 3, 0, 1, 80, 60), (1, 1, 0, 90, 1, 1)),
                        (1, 8, 7, 1, "FM BRASS PAD", 48, 12, 922, (2, 100, 1, 0, 2, 70, 55), (1, 5, 0, 90, 1, 1)),
                        (3, 8, 5, 1, "FM GLASS MID", 60, 12, 923, (1, 90, 2, 0, 2, 75, 50)),
                        (1, 16, 5, 1, "FM BELL MID", 72, 12, 924, (0, 100, 1, 0, 2, 60, 70))],
     5, 4, (95, 40, 80), (7, 50, 45, 35)),
    # factory: a kick, an FM bass loop, clang stabs and a ratcheted mallet, in E phrygian
    ("FACTORY", 126, 4, [(4, 16, 3, 7, "KICK MID", 36, 1, 931, (0, 100, 1, 0, 0, 100, 5)),
                         (6, 16, 3, 8, "FM BASS BRIGHT", 36, 12, 932, (5, 100, 8, 10, 0, 100, 10)),
                         (3, 16, 3, 8, "FM CLANG MID", 60, 12, 933, (0, 90, 1, 0, 0, 70, 40)),
                         (5, 8, 4, 8, "FM MALLET BRIGHT", 72, 12, 934, (4, 100, 1, 0, 0, 65, 35), (3, 0, 0, 90, 3, 2))],
     0, 1, (40, 70, 45), (2, 30, 75, 30)),
]


def resolve(name, index):
    """a sound by name; if that variant was not kept for the shape, the closest one"""
    if name in index:
        return index[name]
    shape = max((n for n in NAMES if name.startswith(n + " ")), key=len)
    want = name[len(shape) + 1:]
    order = {"DARK": ["DARK", "MID", "BRIGHT"], "MID": ["MID", "DARK", "BRIGHT"], "BRIGHT": ["BRIGHT", "MID", "DARK"],
             "PAD": ["PAD", "MID", "DARK"], "PLUCK": ["PLUCK", "MID", "BRIGHT"]}[want]
    for word in order:
        if f"{shape} {word}" in index:
            return index[f"{shape} {word}"]
    raise SystemExit(f"no sound for {name}")


def render(measurements):
    snd = sounds(measurements)
    index = {s["name"]: i for i, s in enumerate(snd)}
    out = ["/* SPDX-License-Identifier: GPL-3.0-only */",
           "/* Generated by tools/gen_presets.py from measurements of the Braids voice. Do not edit by hand. */",
           "#pragma once", "#include <stdint.h>", "",
           "/* type: 0 tone, 1 pluck, 2 pad, 3 drum (the browser's BY TYPE groups) */",
           "typedef struct { const char *name; uint8_t shape, type, attack, release, env; uint16_t timbre, color, gain; } sound_t;",
           "typedef struct {",
           "    uint8_t hits, steps, speed, scale, sound, low, span;     /* rhythm, scale, sound, note range */",
           "    uint8_t algo, chance, amount, mutate, chord, level, send; /* note algorithm, chord follow (0 off 1 scale 2 triad), reverb send */",
           "    uint16_t seed;",
           "    uint8_t feel, rotate, accents, rule, ratchet, subhits;   /* the rhythm source: 0 euclid 1 rotate 2 automaton 3 ratchet */",
    "    uint8_t pan;                                             /* 0 left, 50 middle, 100 right */",
           "} patch_lane_t;",
           "typedef struct {",
           "    const char *name; uint8_t bpm, key, progression, rate, scale_lock;",
           "    uint8_t group;                                            /* the browser's group: 0 demo, 1 song, 2 + mood */",
           "    uint8_t reverb[3];                                        /* decay, brightness, return */",
           "    uint8_t delay[4];                                         /* note value, feedback, tone, return */",
           "    patch_lane_t lane[4];",
           "} patch_t;", "",
           f"#define NSOUNDS {len(snd)}u", "static const sound_t SOUNDS[NSOUNDS] = {"]
    for s in snd:
        out.append(f'    {{"{s["name"]}", {s["shape"]}, {s["type"]}, {s["attack"]}, {s["release"]}, {s["env"]}, {s["timbre"]}, '
                   f'{s["color"]}, {s["gain"]}}},')
    out.append("};\n")
    allp = DEMOS + PATCHES + generated_patches(96)
    assert len(snd) < 256, "patch lanes store the sound number in one byte"
    out.append(f"#define NPATCHES {len(allp)}u")
    out.append(f"#define NDEMO {len(DEMOS)}u                                 /* the first NDEMO patches are the demo songs */")
    out.append("static const patch_t PATCHES[NPATCHES] = {")
    lean = ["import Firmware.Patch", "",
            "/-! Generated by tools/gen_presets.py with voices/presets.h; do not edit. The factory patches as `Patch` values, in",
            "the order the firmware keeps them, so `Proofs/Presets.lean` can check them against `Patch.Fits`. -/", "",
            "/-- The factory patches. -/", "def Presets.all : List Patch := ["]
    for patch in allp:
        name, bpm, key, lanes = patch[:4]
        progression, rate, reverb, delay = (*patch[4:], *((0, 1, (50, 60, 70), (6, 40, 60, 0))[len(patch) - 4:]))
        cells, lanes_lean = [], []
        for pos, lane in enumerate(lanes):
            h, st, sp, sc, snd_name, low, span, seed = lane[:8]
            extra = lane[8] if len(lane) > 8 else HAND_EXTRAS[pos] if span > 1 else (0, 100, 1, 0, 0, 100, ROLE_SEND['hat'])
            feel = lane[9] if len(lane) > 9 else (0, 0, 0, 90, 1, 1)      # feel, rotate, accents, rule, ratchet, sub-hits
            pan = lane[10] if len(lane) > 10 else HAND_PANS[pos]
            cells.append(f"{{{h}, {st}, {sp}, {sc}, {resolve(snd_name, index)}, {low}, {span}, {', '.join(map(str, extra))}, {seed}, "
                         f"{', '.join(map(str, feel))}, {pan}}}")
            values = (h, st, sp, sc, resolve(snd_name, index), low, span, *extra, seed, *feel, pan)
            names = ("hits", "steps", "speed", "scale", "sound", "low", "span", "algo", "chance", "amount", "mutate", "chord",
                     "level", "send", "seed", "feel", "rotate", "accents", "rule", "ratchet", "subHits", "pan")
            lanes_lean.append("{ " + ", ".join(f"{n} := {v}" for n, v in zip(names, values)) + " }")
        group = 0 if patch in DEMOS else 1 if patch in PATCHES else 2 + (allp.index(patch) - len(DEMOS) - len(PATCHES)) % len(MOODS)
        out.append(f'    {{"{name}", {bpm}, {key}, {progression}, {rate}, 0, {group}, {{{", ".join(map(str, reverb))}}}, {{{", ".join(map(str, delay))}}}, {{{", ".join(cells)}}}}},')
        lean.append(f"  {{ bpm := {bpm}, key := {key}, progression := {progression}, rate := {rate}, scaleLock := 0, "
                    f"reverbTime := {reverb[0]}, reverbBright := {reverb[1]}, reverbAmount := {reverb[2]}, "
                    f"delayTime := {delay[0]}, delayFeedback := {delay[1]}, delayTone := {delay[2]}, delayAmount := {delay[3]},")
        for i, l in enumerate(lanes_lean):
            lean.append(f"    lane{i} := {l}" + ("," if i < 3 else " },"))
    out.append("};")
    lean[-1] = lean[-1].rstrip(",")
    lean.append("]")
    return "\n".join(out) + "\n", "\n".join(lean) + "\n"


if __name__ == "__main__":
    text, lean_text = render(audit_voices.all_measurements())
    if "--write" in sys.argv:
        TARGET.write_text(text)
        LEAN_TARGET.write_text(lean_text)
        print(f"wrote {TARGET} and {LEAN_TARGET}")
    elif "--check" in sys.argv:
        if not TARGET.exists() or TARGET.read_text() != text or not LEAN_TARGET.exists() or LEAN_TARGET.read_text() != lean_text:
            print("voices/presets.h or Spec/Presets.lean is out of date: run tools/gen_presets.py --write")
            sys.exit(1)
        nsounds = int(re.search(r"#define NSOUNDS (\d+)u", text).group(1))
        patch_lean = (ROOT / "Firmware/Patch.lean").read_text()
        if f"l.sound < {nsounds} ∧" not in patch_lean or f"{nsounds} sounds" not in patch_lean:
            print(f"Firmware/Patch.lean: PatchLane.Fits must say `l.sound < {nsounds}` (NSOUNDS in voices/presets.h)")
            sys.exit(1)
    else:
        print(text)
