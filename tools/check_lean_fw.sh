#!/bin/sh
# Link the Lean firmware code for the chip with only the small runtime (rt/lean_rt.c) and Init.
# Fails on any undefined symbol, i.e. any Lean feature the runtime does not provide.
set -eu
cd "$(dirname "$0")/.."
T=pi32v2
sh tools/build_lean_fw.sh $T
. tools/target_env.sh
EXPORTS=$(sed -n 's/^@\[export \([A-Za-z0-9_]*\)\].*/\1/p' $(for f in Firmware/*.lean; do echo "$(sh tools/glue_modules.sh)" | grep -qx "$(basename "$f" .lean)" || echo "$f"; done))
[ -n "$EXPORTS" ] || { echo "no @[export] functions in Firmware/"; exit 1; }
$CC -Os -ffunction-sections -w -include stdint.h -c fw/firmware/src/libc.c -o build/lean/$T/libc.o     # memcpy etc., as in the real firmware
set --; for e in $EXPORTS; do set -- "$@" -u "$e"; done
vendor/toolchain/pi32v2/bin/ld --gc-sections -e "${EXPORTS%%
*}" "$@" build/lean/$T/*.o build/init/$T/libInit.a -o build/lean/$T/check.elf
SIZE=$(vendor/toolchain/common/bin/objsizedump build/lean/$T/check.elf 2>/dev/null | tail -3 | tr '\n' ' ')
echo "lean-check OK: Lean firmware code links for the chip. exports: $(echo $EXPORTS | tr '\n' ' ')"
vendor/toolchain/common/bin/objdump -h build/lean/$T/check.elf | awk '$2 ~ /^\.(text|data|bss|rodata|pool)/ {printf "  %s %d B\n", $2, strtonum("0x"$3)}' || true
