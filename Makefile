# make install && make run
# Pinned by: lean-toolchain, lake-manifest.json, requirements.txt, tools/vendor.sh (SHA-256).
# System prerequisites: see README.md.

export PATH := $(HOME)/.elan/bin:$(PATH)

ELAN_INIT_URL := https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh
ROOT := $(CURDIR)
FWENV := JIELI_TOOLCHAIN=$(ROOT)/vendor/toolchain AC79_SDK=$(ROOT)/vendor/ac79 PATH=$(ROOT)/.venv/bin:$(PATH)

.PHONY: install run run-host web build check kernels fw flash-deps clean


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

# Headless run of the app on this computer: fw/build/host/dinghy.wav and screen PNGs, no browser.
run-host:
	cd fw && PATH=$(ROOT)/.venv/bin:$$PATH sh tests/run_host.sh
	@echo "Open fw/build/host/dinghy.wav and fw/build/host/*.png"

# Builds the installable firmware package fw/build/dinghy.fwsc (does NOT flash anything).
fw:
	cd fw && $(FWENV) sh build.sh

# Lean kernels -> C -> JieLi pi32v2 clang; fails if they need the Lean runtime.
kernels:
	sh tools/check_kernels.sh

# Lean kernel replay (Linux, bubblewrap) + chip-compatibility of the kernels.
check: kernels
	lake check

# Only needed to flash from this computer: python MIDI libs for fw/tools/fm1_install.py.
flash-deps:
	.venv/bin/pip install -q -r requirements-flash.txt

clean:
	lake clean
	rm -rf build fw/build
