#!/bin/sh
# The engines ported to Lean against Braids' original C++, on this computer, sample for sample:
#   tests/analog_diff.cc  the analog oscillators, with random sync pulses
#   tests/voice_diff.cc   the whole voice, all 48 shapes
# tests/reference/ holds Braids unchanged; its namespaces are renamed at compile time so both versions can live in
# one program.
set -eu
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
PREFIX=$(lean --print-prefix)
lake build Firmware.AnalogApi
T=build/lean_test
rm -rf $T; mkdir -p $T/gen
cp .lake/build/ir/Firmware/AnalogApi.c $T/gen/AnalogApi.c
CXX="g++ -O2 -std=c++11 -w -DTEST"
REF="-Dbraids=braids_ref -Dstmlib=stmlib_ref -Itests/reference"
for f in analog_oscillator digital_oscillator macro_oscillator resources; do
    $CXX $REF -c tests/reference/braids/$f.cc -o $T/ref_$f.o
done
$CXX $REF -c tests/reference/stmlib/utils/random.cc -o $T/ref_random.o
for f in analog_oscillator digital_oscillator macro_oscillator resources; do
    $CXX -Ivoices -c voices/braids/$f.cc -o $T/lean_$f.o
done
$CXX -Ivoices -c voices/stmlib/utils/random.cc -o $T/lean_random.o
gcc -O2 -w -I"$PREFIX/include" -I$T/gen -c voices/analog_glue.c -o $T/glue.o
for t in analog_diff voice_diff; do
    $CXX -c tests/$t.cc -o $T/$t.o
done
$CXX $REF -c tests/analog_ref_adapter.cc -o $T/analog_ref_adapter.o
$CXX $REF -c tests/voice_ref_adapter.cc -o $T/voice_ref_adapter.o
$CXX -Ivoices -c tests/analog_lean_adapter.cc -o $T/analog_lean_adapter.o
$CXX -Ivoices -c tests/voice_lean_adapter.cc -o $T/voice_lean_adapter.o
SHARED="$T/ref_*.o $T/lean_*.o $T/glue.o"
g++ -o $T/analog_diff $T/analog_diff.o $T/analog_ref_adapter.o $T/analog_lean_adapter.o $SHARED
g++ -o $T/voice_diff $T/voice_diff.o $T/voice_ref_adapter.o $T/voice_lean_adapter.o $SHARED
$T/analog_diff
$T/voice_diff
