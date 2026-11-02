#!/usr/bin/env python3
"""Repo style checks: clean code, no excess comments or proofs, no LLM-sounding prose.
Errors fail `make lint`; warnings are printed. Rules and reasons: agents.md sections 10-12.
Vendored code (fw/, vendor/, voices/braids/, voices/stmlib/) and generated files are not checked."""
import re, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
files = subprocess.check_output(["git", "ls-files", "-co", "--exclude-standard"], cwd=ROOT, text=True).split()
files = [f for f in files if (ROOT / f).is_file()]
skip = ("fw/", "vendor/", "build/", ".lake/", "lake-manifest.json", "voices/braids/", "voices/stmlib/",
        "voices/presets.h", "tests/reference/", "site/coi-serviceworker.min.js")
files = [f for f in files if not f.startswith(skip)]

errors, warnings = [], []
def err(f, n, msg): errors.append(f"{f}:{n}: {msg}")
def warn(f, n, msg): warnings.append(f"{f}:{n}: {msg}")

# Words and phrases that mark machine-written prose. Plain alternatives exist for each.
BANNED = r"""delve|leverag\w+|seamless\w*|robust\w*|comprehensive\w*|cutting-edge|state-of-the-art|game-chang\w+|
holistic\w*|streamlin\w+|elevat\w+|empower\w*|unlock\w*|harness\w*|tapestry|testament|paramount|pivotal|crucial\w*|
meticulous\w*|intricate\w*|myriad|plethora|realm|landscape of|ever-evolving|in today's|it'?s worth noting|
it is worth noting|worth mentioning|importantly,|notably,|furthermore|moreover|additionally,|in conclusion|
in summary|to summarize|let'?s dive|dive into|deep dive|navigate the|under the hood|best practices|
production-ready|battle-tested|blazing|powerful|elegant\w*|simply put|at the end of the day"""
BANNED_RE = re.compile(r"\b(?:" + re.sub(r"\s*\n\s*", "", BANNED) + r")\b", re.I)
SHOUT = re.compile(r"\b(?:CRITICAL|IMPORTANT|MUST NOT FORGET)\b:?")

def prose_check(f, lines, comments_only):
    for i, ln in enumerate(lines, 1):
        if BANNED_RE.search(ln):
            warn(f, i, f"machine-sounding word: '{BANNED_RE.search(ln).group(0)}'. Say it plainly.")
        if re.search(r"\bnot (?:just|only|merely)\b.*\bbut\b", ln, re.I):
            warn(f, i, "'not just X but Y' framing. State the fact.")
        if re.search(r"[\U0001F300-\U0001FAFF\u2600-\u27BF]", ln):
            err(f, i, "emoji")
    text = "\n".join(lines)
    dashes = text.count("\u2014")
    if dashes > max(2, len(lines) // 40):
        warn(f, 1, f"{dashes} em dashes. Use a period, comma or parentheses.")

def md_check(f, lines):
    if f != "agents.md":      # agents.md quotes the banned words
        prose_check(f, lines, False)
    for i, ln in enumerate(lines, 1):
        if SHOUT.search(ln) and f != "agents.md":
            warn(f, i, "shouting label. Plain sentence instead.")
        if len(ln) > 120 and not ln.lstrip().startswith(("|", "http", "[", "```")):
            warn(f, i, "line over 120 characters")
    bullets = sum(1 for l in lines if re.match(r"\s*[-*] \*\*.+?\*\*[:\u2014-]", l))
    if bullets > 12 and f != "agents.md":
        warn(f, 1, f"{bullets} bold-lead bullets. Prose or a table reads better.")

LEAN_BAD = [
    (r"\bsorry\b", "sorry"), (r"\badmit\b", "admit"), (r"^\s*axiom\b", "new axiom"),
    (r"native_decide|bv_decide", "native_decide and bv_decide add an axiom per use"), (r"maxHeartbeats\s+0\b", "maxHeartbeats 0"),
    (r"implemented_by|\bunsafe\b", "implemented_by/unsafe"), (r"skipKernelTC", "skipKernelTC"),
    (r"^\s*partial def", "partial def cannot be reasoned about"),
]

def lean_check(f, lines):
    code = [l for l in lines if not l.strip().startswith("--")]
    defs = theorems = 0
    text = "\n".join(lines)
    for i, ln in enumerate(lines, 1):
        if ln.strip().startswith("--") or ln.lstrip().startswith(("/-", "*")):
            continue
        for pat, what in LEAN_BAD:
            if re.search(pat, ln):
                err(f, i, what)
        if re.match(r"\s*(?:private |protected )?(?:def|abbrev|structure|inductive)\b", ln): defs += 1
        if re.match(r"\s*(?:private |protected )?(?:theorem|lemma)\b", ln): theorems += 1
        if len(ln) > 110: warn(f, i, "line over 110 characters")
    # every declaration needs a docstring on the line above it
    for m in re.finditer(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected )?(def|theorem|structure|inductive|abbrev)\s+(\S+)", text, re.M):
        before = text[:m.start()].rstrip()
        if not before.endswith("-/"):
            warn(f, text[:m.start()].count("\n") + 1, f"{m.group(1)} {m.group(2)} has no docstring")
    # proof layout: theorems live in Proofs/, each public one says why it matters
    in_proofs = f.startswith("Proofs/")
    for m in re.finditer(r"^((?:private )?)(?:theorem|lemma)\s+(\S+)", text, re.M):
        line = text[:m.start()].count("\n") + 1
        if not in_proofs:
            err(f, line, f"theorem {m.group(2)} outside Proofs/. Proofs live in Proofs/<Module>.lean")
        elif not m.group(1):
            before = text[:m.start()].rstrip()
            doc = before[before.rfind("/--"):] if before.endswith("-/") else ""
            if "Why it matters:" not in doc:
                err(f, line, f"public theorem {m.group(2)} needs a docstring with 'Why it matters:'")
            words = [w.lower() for w in re.findall(r"[A-Z][a-z0-9]*", Path(f).stem)]
            if not any(m.group(2).lower().startswith(w) for w in words):
                warn(f, line, f"theorem {m.group(2)} should start with its module name ('{words[-1]}_...')")
    # theorems that prove nothing: `x = x`, or closed by rfl on a name that only restates a definition
    for m in re.finditer(r"theorem\s+(\S+)[^\n]*?\)?\s:\s*([^\n:]+?)\s*:=\s*(?:by\s+)?(rfl|trivial|simp)\s*$", text, re.M):
        lhs = m.group(2)
        eq = re.fullmatch(r"(.+?)\s*=\s*(.+)", lhs)
        if eq and eq.group(1).strip() == eq.group(2).strip():
            err(f, text[:m.start()].count("\n") + 1, f"theorem {m.group(1)} states x = x")
    if defs and theorems > 2 * defs and not f.startswith("Proofs/"):
        warn(f, 1, f"{theorems} theorems for {defs} definitions. Keep only properties someone would want stated.")
    comments = sum(1 for l in lines if l.strip().startswith("--"))
    if len(code) > 20 and comments / max(1, len(code)) > 0.15:
        warn(f, 1, f"{comments} line comments in {len(code)} lines. Names should carry the meaning.")
    prose_check(f, [l for l in lines if l.strip().startswith("--")], True)
    for blk in re.findall(r"/--.*?-/|/-!.*?-/", text, re.S):
        prose_check(f, blk.splitlines(), True)

C_LIKE = (".c", ".h", ".js", ".mjs")
def c_check(f, lines):
    code = comment = 0
    in_block = False
    for i, ln in enumerate(lines, 1):
        s = ln.strip()
        if in_block:
            comment += 1
            if "*/" in s: in_block = False
            continue
        if s.startswith("/*"):
            comment += 1
            in_block = "*/" not in s
        elif s.startswith("//"):
            comment += 1
        elif s:
            code += 1
            if "/*" in s or "//" in s.replace("://", ""): comment += 0.5
        if len(ln) > 140: warn(f, i, "line over 140 characters")
        if re.search(r"\b(TODO|FIXME|XXX|HACK)\b", ln): err(f, i, "TODO/FIXME. Do it or delete it.")
        if re.search(r"console\.log|printf\(\"DEBUG", ln) and "smoke" not in f and "tools/" not in f:
            warn(f, i, "debug print left in")
    if code > 40 and comment / code > 0.35:
        warn(f, 1, f"comment lines are {comment / code:.0%} of code lines. Cut comments that restate the code.")
    blocks = [b for b in re.findall(r"/\*.*?\*/", "\n".join(lines), re.S)]
    for b in blocks: prose_check(f, b.splitlines(), True)
    for i, ln in enumerate(lines, 1):
        if ln.strip().startswith("//") and BANNED_RE.search(ln): warn(f, i, f"machine-sounding word: '{BANNED_RE.search(ln).group(0)}'")

def sh_py_check(f, lines):
    for i, ln in enumerate(lines, 1):
        if re.search(r"\b(TODO|FIXME|XXX|HACK)\b", ln) and "lint.py" not in f: err(f, i, "TODO/FIXME")
        if ln.strip().startswith("#") and BANNED_RE.search(ln): warn(f, i, f"machine-sounding word: '{BANNED_RE.search(ln).group(0)}'")

for f in files:
    p = ROOT / f
    try: lines = p.read_text().splitlines()
    except UnicodeDecodeError: continue
    if f.endswith(".md"): md_check(f, lines)
    elif f == "Challenge.lean": pass      # generated: the statements with sorry for proofs, for Comparator; gen_challenge.py --check keeps it honest
    elif f == "Spec/Presets.lean": pass   # generated data (gen_presets.py --check keeps it with presets.h); its lines are long
    elif f.endswith(".lean"): lean_check(f, lines)
    elif f.endswith(C_LIKE): c_check(f, lines)
    elif f.endswith((".sh", ".py", "Makefile", ".toml")): sh_py_check(f, lines)
    # hygiene
    if lines and any(l != l.rstrip() for l in lines): warn(f, 1, "trailing whitespace")

for root, lib in (("Proofs.lean", "Proofs"), ("Firmware.lean", "Firmware"), ("Spec.lean", "Spec"), ("Examples.lean", "Examples")):
    imported = set(re.findall(rf"^import {lib}\.(\S+)", (ROOT / root).read_text(), re.M))
    for missing in sorted(p.stem for p in (ROOT / lib).glob("*.lean") if p.stem not in imported):
        errors.append(f"{root} does not import {lib}.{missing}, so `lake build` and Comparator never see it")
if subprocess.run([sys.executable, str(ROOT / "tools/gen_challenge.py"), "--check"], cwd=ROOT).returncode:
    errors.append("Challenge.lean or comparator.json is out of date")
if subprocess.run([sys.executable, str(ROOT / "tools/proof_index.py"), "--check"], cwd=ROOT).returncode:
    errors.append("docs/PROOFS.md is out of date")
for script in (["tools/gen_alfred.py", "--check"], ["tools/gen_presets.py", "--check"], ["tools/gen_tables.py", "--check"],
               ["tools/braids_tables.py", "--rate", "44100", "--check"]):
    if subprocess.run([sys.executable, *script], cwd=ROOT, stdout=subprocess.DEVNULL).returncode:
        errors.append(f"{' '.join(script)} failed: regenerate with --write")
for w in warnings: print("warn ", w)
for e in errors: print("ERROR", e)
print(f"lint: {len(files)} files, {len(errors)} errors, {len(warnings)} warnings")
sys.exit(1 if errors else 0)
