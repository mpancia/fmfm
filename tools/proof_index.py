#!/usr/bin/env python3
"""List what the repo proves: every public theorem in Proofs/ with its one-line claim and its reason.
  tools/proof_index.py            print the index
  tools/proof_index.py --write    write docs/PROOFS.md and the "What is proved" section of README.md
  tools/proof_index.py --check    fail if either is out of date (make lint runs this)
The README section groups the modules (GROUPS below); a proof module in no group is an error, so each new
module is placed on purpose."""
import re, sys, textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAT = re.compile(r"/--((?:(?!-/).)*)-/\s*theorem\s+(\S+)", re.S)

# README groups: (title, what the group protects, modules in order)
GROUPS = [
    ("The sequencer",
     "The four lanes. No note is left sounding when you stop, the lanes stay in phase, a bar plays exactly the "
     "hits set, and every note is in the scale and the range.",
     ["Lane", "Run", "Rhythm", "Swing", "Divider", "Euclid", "Notes", "Quantizer", "Random", "Harmony", "Tonnetz", "Arp", "Machine",
      "Lfo", "Punch", "Keys", "KeysChord", "PunchMix", "Clock"]),
    ("The voices",
     "Braids' engines in Lean, the FM voice, the 808 and the filter. Table reads stay inside their tables, the "
     "facts about the tables are checked, and a sample is the arithmetic clipped, not wrapped, except where Braids "
     "itself overflows (docs/LEAN-ENGINES.md).",
     ["Pitch", "Tables", "BraidsData", "Fm", "FmLock", "FmSymmetry", "FmEnvelope", "FmAlgorithms", "FmDeviation",
      "FmRange", "Drum", "Analog", "Digital", "Blend", "Filters", "Filter", "Noise", "Percussion", "Physical",
      "Vowels", "Wavetables"]),
    ("Setting a voice up",
     "Per-note and per-block setup: parameters land in range, smoothing does not overshoot, table reads are "
     "in bounds.",
     ["VoiceSetup", "Smooth", "AnalogSetup", "DigitalSetup", "MacroSetup", "FiltersSetup", "NoiseSetup",
      "PercussionSetup", "PhysicalSetup", "VowelsSetup", "WavetablesSetup"]),
    ("The mix and the effects",
     "The mix does not wrap, the reverb and delay stay inside their lines, their gains are below one so tails "
     "die away, and their filters do not overshoot.",
     ["Mix", "Reverb", "Delay"]),
    ("Patches",
     "A saved patch loads back as saved, anything else in a slot is rejected, and every factory patch is in range.",
     ["Patch", "Presets"]),
]
BEGIN, END = "<!-- proofs:begin -->", "<!-- proofs:end -->"

HEADER = re.compile(r"^theorem (\w+)", re.M)


def statements(text):
    """each public theorem's statement: from its name to the `:=` that starts the proof (a `let x :=` inside the
    statement is not that one)"""
    out = []
    for m in HEADER.finditer(text):
        pos = m.end()
        while True:
            at = text.find(":=", pos)
            if at < 0:
                break
            line = text[text.rfind("\n", 0, at) + 1:at]
            if re.search(r"\blet \w+\s*$", line):
                pos = at + 2
                continue
            out.append((m.group(1), text[m.end():at]))
            break
    return out
IDENT = re.compile(r"\b([A-Z][A-Za-z0-9]*(?:\.[A-Za-z][A-Za-z0-9']*)+)")   # Module.name identifiers in it


DEF = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private )?(?:def|abbrev)\s+(\S+)", re.M)


def definitions():
    """every definition in Firmware/ and Spec/, by name (the C entries have no namespace: `harmonyMask`)"""
    names = set()
    for folder in ("Firmware", "Spec"):
        for path in (ROOT / folder).glob("*.lean"):
            names |= set(DEF.findall(path.read_text()))
    return names


def surfaces(text, defs, module):
    """the definitions each public theorem's statement mentions: its spec surface (the rule: a theorem means what
    its statement says, and the statement means what every definition it mentions means)"""
    found = {}
    for name, statement in statements(text):
        idents = {i for i in IDENT.findall(statement)
                  if not i.startswith(("UInt", "Int", "Nat.", "List.", "Fin.", "Bool.", "Option", "Prod"))}
        idents |= {w for w in re.findall(r"\b[a-z]\w*\b", statement) if w in defs}
        by_short = {}
        for d in defs:                                     # dot notation: `l.silence` is `Lane.silence`
            if "." in d:
                by_short.setdefault(d.rsplit(".", 1)[1], set()).add(d)
        for short in re.findall(r"\b[a-z]\w*\.([a-z]\w*)", statement):
            candidates = by_short.get(short, set())
            own = {d for d in candidates if d.startswith(module + ".")}   # the proof file's own module first
            if len(own) == 1 or len(candidates) == 1:
                idents |= own or candidates
        found[name] = sorted(idents)
    return found


def collect():
    rows = []
    defs = definitions()
    for path in sorted((ROOT / "Proofs").glob("*.lean")):
        text = path.read_text()
        surface = surfaces(text, defs, path.stem)
        for doc, name in PAT.findall(text):
            doc = " ".join(doc.split())
            claim, _, why = doc.partition("Why it matters:")
            rows.append((path.stem, name, claim.strip(), why.strip(), surface.get(name, [])))
    return rows

def wrap(text):
    return textwrap.fill(text, width=120, break_long_words=False, break_on_hyphens=False)

def render(rows):
    out = ["# What is proved", "",
           "Generated by `tools/proof_index.py --write`; `make lint` fails if it is out of date.",
           "One entry per public theorem in `Proofs/`. The spec surface is the definitions the statement uses, in",
           "`Firmware/` (the code) and `Spec/` (definitions needed to state it). `Examples/Sequencer.lean` and",
           "`Examples/Voices.lean` instantiate every theorem on concrete inputs.", ""]
    module = None
    for mod, name, claim, why, surface in rows:
        if mod != module:
            out += [f"## {mod}", ""]
            module = mod
        out += [wrap(f"**`{name}`**: {claim}"), ""]
        if why:
            out += [wrap(f"Why it matters: {why}"), ""]
        if surface:
            out += [wrap("Spec surface: " + ", ".join(f"`{d}`" for d in surface)), ""]
    return "\n".join(out).rstrip() + "\n"

def sentence(text):
    """The first sentence, so a table cell stays short."""
    return re.split(r"(?<=[.!?])\s", text, maxsplit=1)[0].rstrip(".") + "." if text else ""

def render_readme(rows):
    placed = {m for _, _, mods in GROUPS for m in mods}
    missing = sorted({m for m, _, _, _, _ in rows} - placed)
    if missing:
        print(f"proof_index: add {', '.join(missing)} to a GROUPS entry in tools/proof_index.py"); sys.exit(1)
    by_module = {}
    for mod, name, claim, why, _ in rows:
        by_module.setdefault(mod, []).append((name, claim, why))
    out = [BEGIN,
           f"{len(rows)} theorems, checked by Lean's kernel and by `make comparator`. Generated from the docstrings",
           "in `Proofs/` by `make proofs`; `docs/PROOFS.md` has the full statements.", ""]
    for title, about, mods in GROUPS:
        count = sum(len(by_module.get(m, [])) for m in mods)
        if not count:
            continue
        out += [f"<details><summary><b>{title}</b>: {count} theorems</summary>", "", wrap(about), "",
                "| Theorem | Says | Protects against |", "|---|---|---|"]
        for m in mods:
            for name, claim, why in by_module.get(m, []):
                out.append(f"| `{name}` | {sentence(claim)} | {sentence(why)} |")
        out += ["", "</details>", ""]
    return "\n".join(out).rstrip() + "\n" + END

def readme_with(section):
    text = (ROOT / "README.md").read_text()
    if BEGIN not in text or END not in text:
        print("README.md has no <!-- proofs:begin --> ... <!-- proofs:end --> section"); sys.exit(1)
    head, rest = text.split(BEGIN, 1)
    _, tail = rest.split(END, 1)
    return head + section + tail

if __name__ == "__main__":
    rows = collect()
    text = render(rows)
    target = ROOT / "docs" / "PROOFS.md"
    readme = readme_with(render_readme(rows))
    if "--write" in sys.argv:
        target.write_text(text)
        (ROOT / "README.md").write_text(readme)
    elif "--check" in sys.argv:
        if not target.exists() or target.read_text() != text:
            print("docs/PROOFS.md is out of date: run tools/proof_index.py --write"); sys.exit(1)
        if (ROOT / "README.md").read_text() != readme:
            print("README.md's What is proved section is out of date: run tools/proof_index.py --write"); sys.exit(1)
    else:
        print(text)
