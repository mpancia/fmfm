#!/bin/sh
# The engines ported to Lean against Braids' original C++, on this computer, sample for sample:
#   tests/analog_diff.cc  the analog oscillators, with random sync pulses
#   tests/voice_diff.cc   the whole voice, all 48 shapes
#   tests/reverb_diff.cc  the reverb send against Clouds' original, as an error in dB (it is fixed-point, so not exact)
# tests/reference/ holds Braids unchanged; its namespaces are renamed at compile time so both versions can live in
# one program.
set -eu
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
PREFIX=$(lean --print-prefix)
for m in $(sh tools/glue_modules.sh | grep Api); do lake build "Firmware.$m"; done
T=${LEAN_TEST_DIR:-build/lean_test}
rm -rf $T; mkdir -p $T/gen
for m in $(sh tools/glue_modules.sh | grep Api); do cp .lake/build/ir/Firmware/$m.c $T/gen/$m.c; done
CXX="g++ -O2 -std=c++11 -w -DTEST"
REF="-Dbraids=braids_ref -Dstmlib=stmlib_ref -Itests/reference"
for f in analog_oscillator digital_oscillator macro_oscillator resources; do
    $CXX $REF -c tests/reference/braids/$f.cc -o $T/ref_$f.o
done
$CXX $REF -c tests/reference/stmlib/utils/random.cc -o $T/ref_random.o
for src in voices/braids/*.cc; do
    $CXX -Ivoices -c $src -o $T/lean_$(basename $src .cc).o
done
$CXX -Ivoices -c voices/stmlib/utils/random.cc -o $T/lean_random.o
for g in voices/*_glue.c fx/*_glue.c; do
    gcc -O2 -w -I"$PREFIX/include" -I$T/gen -I$(dirname $g) -c $g -o $T/glue_$(basename $g .c).o
done
for t in analog_diff voice_diff; do
    $CXX -c tests/$t.cc -o $T/$t.o
done
$CXX $REF -c tests/analog_ref_adapter.cc -o $T/analog_ref_adapter.o
$CXX $REF -c tests/voice_ref_adapter.cc -o $T/voice_ref_adapter.o
$CXX -Ivoices -c tests/analog_lean_adapter.cc -o $T/analog_lean_adapter.o
$CXX -Ivoices -c tests/voice_lean_adapter.cc -o $T/voice_lean_adapter.o
SHARED="$T/ref_*.o $T/lean_*.o $T/glue_*.o"
g++ -o $T/analog_diff $T/analog_diff.o $T/analog_ref_adapter.o $T/analog_lean_adapter.o $SHARED
g++ -o $T/voice_diff $T/voice_diff.o $T/voice_ref_adapter.o $T/voice_lean_adapter.o $SHARED
$CXX -Dclouds=clouds_ref -Dstmlib=stmlib_ref -Itests/reference -Ifx -c tests/reverb_diff.cc -o $T/reverb_diff.o
g++ -o $T/reverb_diff $T/reverb_diff.o $T/glue_reverb_glue.o
$T/analog_diff
$T/voice_diff
$T/reverb_diff
