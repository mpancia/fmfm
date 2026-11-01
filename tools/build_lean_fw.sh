#!/bin/sh
# Compile the Lean code that runs on the FM-1 for one target:
#   tools/build_lean_fw.sh wasm32|pi32v2|host   ->  build/lean/<target>/*.o  and  build/init/<target>/libInit.a
# Inputs: Firmware/*.lean (via lake, which writes the C), rt/lean_rt.c (the small runtime).
set -eu
cd "$(dirname "$0")/.."
T=${1:?target: wasm32, pi32v2 or host}
. tools/target_env.sh
lake build Firmware
sh tools/build_lean_init.sh "$T"
O=build/lean/$T
rm -rf "$O"; mkdir -p "$O"
# The modules that voices/*_glue.c include as inline functions are not built here.
SKIP=$(sh tools/glue_modules.sh)
for c in .lake/build/ir/Firmware/*.c rt/lean_rt.c; do
    if echo "$SKIP" | grep -qx "$(basename "$c" .c)"; then continue; fi
    $CC -Os -ffunction-sections -Wall -Wno-unused-parameter -c "$c" -o "$O/$(basename "$(dirname "$c")")_$(basename "$c" .c).o"
done
echo "lean: $(ls "$O"/*.o | wc -l) objects in $O"
