#!/bin/sh
# Build Lean's own library (Init) as a static archive for a target the toolchain does not ship it for.
#   tools/build_lean_init.sh wasm32|pi32v2     ->  build/init/<target>/libInit.a
# Lean-generated C calls library functions (List.reverse, Array.erase, ...) that live in Init. We generate C
# for every Init module with the pinned `lean` (extract_closed off, so no module initialisation is needed) and
# compile it for the target. The linker then takes only the archive members the firmware actually uses.
set -eu
cd "$(dirname "$0")/.."
T=${1:?target: wasm32 or pi32v2}
. tools/target_env.sh
STAMP=$(lean --version | head -1)
C=build/init/c; O=build/init/$T
mkdir -p "$C" "$O"
if [ "$(cat build/init/c.stamp 2>/dev/null)" != "$STAMP" ]; then
    rm -rf build/init; mkdir -p "$C" "$O"
    (cd "$PREFIX/src/lean" && find Init -name '*.lean' | sort) > build/init/modules.txt
    echo "generating C for $(wc -l < build/init/modules.txt) Init modules"
    ABS=$PWD/$C
    ( cd "$PREFIX/src/lean" && xargs -P "$(nproc)" -I{} sh -c \
        'f={}; lean -D compiler.extract_closed=false -c "'"$ABS"'/$(echo ${f%.lean} | tr / .).c" --root=. "$f"' ) < "$PWD/build/init/modules.txt"
    echo "$STAMP" > build/init/c.stamp
fi
if [ ! -f "$O/libInit.a" ] || [ "$(cat "$O/stamp" 2>/dev/null)" != "$STAMP" ]; then
    rm -f "$O"/*.o "$O/libInit.a"
    # JieLi's clang 4.0.1 crashes on a few modules (Init.Tactics, Init.Data.Order.PackageFactories: no code
    # firmware needs). Those are skipped; if firmware code ever needs one, the link reports the missing symbol.
    ls "$C"/*.c | xargs -P "$(nproc)" -I{} sh -c '$0 -Os -ffunction-sections -w -c {} -o '"$O"'/$(basename {} .c).o >/dev/null 2>&1 || { rm -f '"$O"'/$(basename {} .c).o; echo "init: skipped $(basename {}) (compiler failed)"; }' "$CC"
    "$AR" rcs "$O/libInit.a" "$O"/*.o
    rm -f "$O"/*.o
    echo "$STAMP" > "$O/stamp"
fi
echo "init: $O/libInit.a ($(wc -c < "$O/libInit.a") B)"
