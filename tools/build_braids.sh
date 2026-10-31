#!/bin/sh
# Compile the Braids voice (voices/: Braids and stmlib sources, shims, voice.cc) for one target:
#   tools/build_braids.sh wasm32|pi32v2   ->  build/braids/<target>/*.o
# Braids is C++ written for a chip with no standard library; voices/shim/ supplies the few headers it names.
set -eu
cd "$(dirname "$0")/.."
T=${1:?target: wasm32 or pi32v2}
. tools/target_env.sh
O=build/braids/$T
rm -rf "$O"; mkdir -p "$O" build/lean_gen
for g in voices/*_glue.c; do                                          # the arithmetic in Lean, included as inline C
    api=$(sed -n 's/^#include "\([A-Za-z0-9]*Api\)\.c"/\1/p' "$g")
    lake build "Firmware.$api"
    cp ".lake/build/ir/Firmware/$api.c" "build/lean_gen/$api.c"
    $CC -Os -ffunction-sections -w -Ibuild/lean_gen -c "$g" -o "$O/voices_$(basename "$g" .c).o"
done
for src in voices/braids/*.cc voices/stmlib/utils/random.cc voices/voice.cc; do
    $CXX -std=c++11 -O2 -fno-exceptions -fno-rtti -Ivoices/shim -Ivoices -DTEST -w \
        -c "$src" -o "$O/$(basename "$(dirname "$src")")_$(basename "$src" .cc).o"
done
echo "braids: $(ls "$O"/*.o | wc -l) objects in $O"
