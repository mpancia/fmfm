#!/bin/sh
# Compile the firmware app (fw/firmware/src/dinghy.c, DINGHY_WEB build) plus the Lean code and its runtime to
# WebAssembly with the clang and lld inside the pinned Lean toolchain, and assemble the page into build/web/.
# No emscripten, no libc: web/web_host.c is the platform.
set -eu
cd "$(dirname "$0")/.."
T=wasm32
sh tools/build_lean_fw.sh $T
sh tools/build_braids.sh $T
. tools/target_env.sh
OUT=${WEB_OUT:-build/web}                              # WEB_OUT and WEB_DEFS: a variant build, e.g. tools/preview_looks.py
mkdir -p "$OUT" build/bin
ln -sf "$PREFIX/bin/ld.lld" build/bin/wasm-ld         # lld picks its wasm personality from its own name
(cd fw && $CC -O2 -Wall -Wno-unused-function -DDINGHY_WEB -DAPP_VER='"web"' ${WEB_DEFS:-} \
    -Ifirmware/hal -Ifirmware/src -Ifirmware/gen -I../voices -I../ui -I../fx -c firmware/src/dinghy.c -o ../build/dinghy_web.o)
build/bin/wasm-ld --no-entry --export=web_run --export=web_in_ptr --export=web_harmony_mask -z stack-size=1048576 \
    build/dinghy_web.o build/lean/$T/*.o build/braids/$T/*.o build/init/$T/libInit.a -o "$OUT/dinghy.wasm"
cp web/index.html web/sim.css web/sim.js web/worker.js web/worklet.js "$OUT/"
echo "web: $OUT ($(wc -c < "$OUT/dinghy.wasm") B wasm)"
