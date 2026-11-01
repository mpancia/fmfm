#!/bin/sh
# The firmware on this computer (fw/tests/host.c, Dinghy's host mode) with the Lean code and the Braids voice
# linked in natively, counting the instructions each sample costs (Linux perf counters):
#   tools/perf_host.sh [script.txt]     -> build/host/perf.wav and "perf N instructions / sample"
# Dinghy's yardstick: sloopDX's engines measured here at about 1000-1500 instructions a sample and fit the FM-1's
# audio interrupt. The chip has its own instruction set, so this is a ratio, not a cycle count (docs/BUDGET.md).
set -eu
cd "$(dirname "$0")/.."
T=host
. tools/target_env.sh
sh tools/build_lean_fw.sh $T >/dev/null
sh tools/build_braids.sh $T >/dev/null
mkdir -p build/host
$CC -O2 -DDINGHY_HOST -DAPP_VER='"host"' -Ifw/firmware/hal -Ifw/firmware/src -Ifw/firmware/gen -Ivoices -Iui -Ifx \
    -c fw/firmware/src/dinghy.c -o build/host/dinghy.o
# GNU ld pulls whole Init members, whose module initialisers name the full Lean runtime; they are never called
# (extract_closed is off), so unresolved names are allowed and gc-sections drops them. nm then checks that no
# Lean runtime symbol stayed undefined in what is left.
c++ -m32 -o build/host/perf build/host/dinghy.o build/lean/$T/*.o build/braids/$T/*.o build/init/$T/libInit.a \
    -Wl,--gc-sections -Wl,--unresolved-symbols=ignore-all
if nm -u build/host/perf | grep -q " lean_\| initialize_"; then echo "perf_host: live code needs runtime symbols:"; nm -u build/host/perf | grep " lean_\| initialize_"; exit 1; fi
DINGHY_PERF=1 build/host/perf build/host/perf ${1:+"$1"}
