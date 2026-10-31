#!/bin/sh
# Compile the firmware app (fw/firmware/src/dinghy.c, DINGHY_WEB build) to WebAssembly with the clang and
# lld that ship inside the pinned Lean toolchain, and assemble the page into build/web/.
# No emscripten, no libc: web/web_host.c is the platform.
set -eu
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
PREFIX=$(lean --print-prefix)
OUT=build/web
mkdir -p "$OUT" build/bin
ln -sf "$PREFIX/bin/ld.lld" build/bin/wasm-ld         # lld picks its wasm personality from its own name
(cd fw && "$PREFIX/bin/clang" --target=wasm32 -O2 -ffreestanding -nostdlib -isystem "$PREFIX/include/clang" \
    -Wall -Wno-unused-function -DDINGHY_WEB -DAPP_VER='"web"' \
    -Ifirmware/hal -Ifirmware/src -Ifirmware/gen -c firmware/src/dinghy.c -o ../build/dinghy_web.o)
build/bin/wasm-ld --no-entry --export=web_run --export=web_in_ptr -z stack-size=1048576 \
    build/dinghy_web.o -o "$OUT/dinghy.wasm"
cp web/index.html web/sim.css web/sim.js web/worker.js web/worklet.js "$OUT/"
echo "web: $OUT ($(wc -c < "$OUT/dinghy.wasm") B wasm)"
