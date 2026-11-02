# make install && make run
# Pinned by: lean-toolchain, lake-manifest.json, requirements.txt, tools/vendor.sh (SHA-256).
# System prerequisites: see README.md.

export PATH := $(HOME)/.elan/bin:$(PATH)

ELAN_INIT_URL := https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh
ROOT := $(CURDIR)

.PHONY: install run web pitch video test test-lean test-exports audit build check lean-check fw flash-deps clean lint proofs comparator perf


install:
	@for c in git curl python3 cc; do command -v $$c >/dev/null || { echo "missing system package: $$c (see README.md)"; exit 1; }; done
	@command -v elan >/dev/null || { echo "Installing elan..."; \
	  curl -sSfL $(ELAN_INIT_URL) | sh -s -- -y --default-toolchain none --no-modify-path; }
	@if [ "$$(uname -s)" = Linux ] && ! command -v bwrap >/dev/null; then \
	  echo "warning: bubblewrap not found; 'make check' will fail (see README.md)"; fi
	@[ -x .venv/bin/python ] || python3 -m venv .venv
	.venv/bin/pip install -q -r requirements.txt
	sh tools/vendor.sh
	lake build

# The simulator: the firmware compiled to WebAssembly, in a page with the FM-1's screen, keys, knobs and audio.
# Serves http://localhost:8000/ until Ctrl-C. Needs a Chromium-based browser (or Firefox) with Web Audio.
run: web
	python3 tools/serve_web.py 8000 build/web

web:
	sh tools/build_web.sh

# The five-minute pitch deck (site/pitch, docs/PITCH.md is the run-sheet): build/pitch/index.html, open it in a browser.
pitch: web
	.venv/bin/python tools/make_pitch.py

# The demo film, about a minute and a half: build/video/formalfred.mp4 (and .webm); one song from four presets played
# at once by four runs of the firmware, mixed as an arrangement, with chapter cards. Needs ffmpeg.
video: web
	.venv/bin/python tools/make_video.py

# Headless tests of the web build: boots the firmware in node, plays notes, checks sound, screen and LEDs; renders
# every demo song and checks its level; plays every factory patch and fails on clipping or silence.
test: web
	node tools/smoke_web.mjs
	node tools/smoke_demos.mjs
	node tools/check_patches.mjs

# Builds the installable firmware package fw/build/dinghy.fwsc (does NOT flash anything).
# Includes the Lean code from Firmware/ and its runtime (rt/).
fw:
	sh tools/build_fw.sh

# The Lean code that runs on the FM-1 links for the chip with only the small runtime.
lean-check:
	sh tools/check_lean_fw.sh

# The engines ported to Lean against Braids' original C++, sample for sample (tests/reference is Braids unchanged).
test-lean:
	sh tools/test_lean_engines.sh

# The compiler, checked: every scalar Lean export compiled to C and built for this computer, run on random inputs,
# and the kernel asked whether the definitions give the same values (tools/check_exports.py).
test-exports:
	python3 tools/check_exports.py

# The firmware on this computer with Linux perf counters: instructions a sample (docs/BUDGET.md).
perf:
	sh tools/perf_host.sh

# Renders every factory sound on this computer: each must be audible, not clip, and keep its level across octaves.
audit:
	python3 tools/audit_voices.py --check

# Lists every public theorem with what it claims and why (also written to docs/PROOFS.md), and regenerates
# the Comparator challenge (Challenge.lean, comparator.json) from the same theorems.
proofs:
	python3 tools/proof_index.py --write
	python3 tools/gen_challenge.py
	@cat docs/PROOFS.md

# Comparator: Proofs/ proves every statement in Challenge.lean, with no axiom but the three standard ones,
# and the kernel accepts it (Linux, bubblewrap). PARANOID=1 also runs the five external checkers.
comparator:
	lake comparator $(if $(PARANOID),--paranoid)

# Style checks: sorry/axioms, undocumented or pointless theorems, excess comments, machine-sounding prose.
lint:
	python3 tools/lint.py

# Lint, the chip link check, the differential tests, then Comparator (Linux, bubblewrap).
check: lint lean-check test-lean test-exports comparator

# Only needed to flash from this computer: python MIDI libs for fw/tools/fm1_install.py.
flash-deps:
	.venv/bin/pip install -q -r requirements-flash.txt

clean:
	lake clean
	rm -rf build fw/build
