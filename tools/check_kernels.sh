#!/bin/sh
# Compile the C that Lean generates for Fmfm.Kernels with JieLi's pi32v2 clang and
# link it with --gc-sections. Fails if any exported kernel still needs the Lean runtime.
set -eu
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
TC=vendor/toolchain/pi32v2/bin
lake build Fmfm.Kernels
C=.lake/build/ir/Fmfm/Kernels.c
EXPORTS=$(sed -n 's/^@\[export \([a-z0-9_]*\)\].*/\1/p' Fmfm/Kernels.lean)
[ -n "$EXPORTS" ] || { echo "no @[export] kernels found"; exit 1; }
mkdir -p build
$TC/clang -target pi32v2 -Os -ffunction-sections -fno-builtin \
    -I"$(lean --print-prefix)/include" -c "$C" -o build/Kernels.o
set --; for e in $EXPORTS; do set -- "$@" -u "$e"; done
$TC/ld --gc-sections -e "${EXPORTS%%
*}" "$@" build/Kernels.o -o build/Kernels.elf
echo "kernels OK (no Lean runtime needed): $EXPORTS"
