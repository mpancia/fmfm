#!/bin/sh
# Build the installable package fw/build/dinghy.fwsc: Dinghy's build, with the Lean code and runtime linked in.
set -eu
cd "$(dirname "$0")/.."
T=pi32v2
sh tools/build_lean_fw.sh $T
sh tools/build_braids.sh $T
. tools/target_env.sh
ROOT=$PWD
cd fw
JIELI_TOOLCHAIN=$ROOT/vendor/toolchain AC79_SDK=$ROOT/vendor/ac79 PATH=$ROOT/.venv/bin:$PATH \
DINGHY_DEFS="-I$PREFIX/include -I$ROOT/rt -I$ROOT/voices" \
DINGHY_LINK="$(echo $ROOT/build/lean/$T/*.o $ROOT/build/braids/$T/*.o) $ROOT/build/init/$T/libInit.a" \
    sh build.sh
