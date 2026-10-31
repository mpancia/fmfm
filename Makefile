# Usage: make install && make run
# Everything is pinned by `lean-toolchain` (Lean) and `lake-manifest.json` (Lake deps).
# System prerequisites: see README.md.

export PATH := $(HOME)/.elan/bin:$(PATH)

ELAN_INIT_URL := https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh

.PHONY: install run build check clean

# Installs elan (Lean version manager) into ~/.elan if missing, then fetches the
# pinned toolchain and builds the project. Needs no sudo.
install:
	@command -v git  >/dev/null || { echo "missing system package: git (see README.md)";  exit 1; }
	@command -v curl >/dev/null || { echo "missing system package: curl (see README.md)"; exit 1; }
	@command -v elan >/dev/null || { \
	  echo "Installing elan..."; \
	  curl -sSfL $(ELAN_INIT_URL) | sh -s -- -y --default-toolchain none --no-modify-path; }
	@if [ "$$(uname -s)" = Linux ] && ! command -v bwrap >/dev/null; then \
	  echo "warning: bubblewrap (bwrap) not found; 'make check' will not work (see README.md)"; fi
	lake build

run:
	lake exe fmfm

build:
	lake build

# Replays the build through Lean's kernel and rejects non-standard axioms.
# Linux only; needs bubblewrap.
check:
	lake check

clean:
	lake clean
