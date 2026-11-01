#!/bin/sh
# Link the Lean firmware code for the chip with only the small runtime (rt/lean_rt.c) and Init.
# Fails on any undefined symbol, i.e. any Lean feature the runtime does not provide.
set -eu
cd "$(dirname "$0")/.."
T=pi32v2
sh tools/build_lean_fw.sh $T
. tools/target_env.sh
# A definition with no arguments becomes a global that only the module initialiser fills, and the firmware runs
# no initialisers: it would be read as nil. Fail if any generated code reads one.
for g in $(sed -n 's/^LEAN_EXPORT lean_object\* \(lp_[A-Za-z0-9_]*\);$/\1/p' .lake/build/ir/Firmware/*.c | sort -u); do
    if grep -h "$g" .lake/build/ir/Firmware/*.c | grep -v "^LEAN_EXPORT\|_init_$g\|lean_mark_persistent($g)" | grep -q .; then
        echo "lean-check: $g is a global filled by a module initialiser and read by firmware code; make it a function"
        exit 1
    fi
done
EXPORTS=$(sed -n 's/^@\[export \([A-Za-z0-9_]*\)\].*/\1/p' $(for f in Firmware/*.lean; do echo "$(sh tools/glue_modules.sh)" | grep -qx "$(basename "$f" .lean)" || echo "$f"; done))
[ -n "$EXPORTS" ] || { echo "no @[export] functions in Firmware/"; exit 1; }
mkdir -p build/lean/check                        # not build/lean/$T: build_fw.sh links everything there, and libc.o would be a duplicate
$CC -Os -ffunction-sections -w -include stdint.h -c fw/firmware/src/libc.c -o build/lean/check/libc.o     # memcpy etc., as in the real firmware
set --; for e in $EXPORTS; do set -- "$@" -u "$e"; done
vendor/toolchain/pi32v2/bin/ld --gc-sections -e "${EXPORTS%%
*}" "$@" build/lean/$T/*.o build/lean/check/libc.o build/init/$T/libInit.a -o build/lean/check/check.elf
# Init has the same kind of globals (l_ByteArray_empty, ...); one that survives --gc-sections is read by linked code.
LEAN_GLOBALS=$(vendor/toolchain/common/bin/objdump -t build/lean/check/check.elf \
    | awk '($3 ~ /^\.(bss|data)/ || $4 ~ /^\.(bss|data)/) && $NF ~ /^(l|lp)_/ {print $NF}' | sort -u)
if [ -n "$LEAN_GLOBALS" ]; then
    echo "lean-check: $(echo $LEAN_GLOBALS) are globals only a module initialiser fills and are read by linked code"
    exit 1
fi
SIZE=$(vendor/toolchain/common/bin/objsizedump build/lean/check/check.elf 2>/dev/null | tail -3 | tr '\n' ' ')
echo "lean-check OK: Lean firmware code links for the chip. exports: $(echo $EXPORTS | tr '\n' ' ')"
vendor/toolchain/common/bin/objdump -h build/lean/check/check.elf | awk '$2 ~ /^\.(text|data|bss|rodata|pool)/ {printf "  %s %d B\n", $2, strtonum("0x"$3)}' || true
