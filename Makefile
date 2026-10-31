# make install && make run
# Pinned by: lean-toolchain, lake-manifest.json, requirements.txt, tools/vendor.sh (SHA-256).
# System prerequisites: see README.md.

export PATH := $(HOME)/.elan/bin:$(PATH)

ELAN_INIT_URL := https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh
ROOT := $(CURDIR)

.PHONY: install run web test audit build check lean-check fw flash-deps clean lint proofs


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

# Headless test of the web build: boots the firmware in node, plays notes, checks sound, screen and LEDs.
test: web
	node tools/smoke_web.mjs

# Builds the installable firmware package fw/build/dinghy.fwsc (does NOT flash anything).
# Includes the Lean code from Firmware/ and its runtime (rt/).
fw:
	sh tools/build_fw.sh

# The Lean code that runs on the FM-1 links for the chip with only the small runtime.
lean-check:
	sh tools/check_lean_fw.sh

# Renders every factory sound on this computer: each must be audible, not clip, and keep its level across octaves.
audit:
	python3 tools/audit_voices.py --check

# Lists every public theorem with what it claims and why (also written to docs/PROOFS.md).
proofs:
	python3 tools/proof_index.py --write
	@cat docs/PROOFS.md

# Style checks: sorry/axioms, undocumented or pointless theorems, excess comments, machine-sounding prose.
lint:
	python3 tools/lint.py

# Lint, then Lean kernel replay (Linux, bubblewrap) + the chip link check.
check: lint lean-check
	lake check

# Only needed to flash from this computer: python MIDI libs for fw/tools/fm1_install.py.
flash-deps:
	.venv/bin/pip install -q -r requirements-flash.txt

clean:
	lake clean
	rm -rf build fw/build
