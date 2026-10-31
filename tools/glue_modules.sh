#!/bin/sh
# The Lean modules that voices/*_glue.c and fx/*_glue.c include as inline C, one per line: each Api module, then its
# base module. A glue file may include several (its engine's and SmoothApi).
#   tools/glue_modules.sh        e.g. AnalogApi / Analog / SmoothApi / Smooth
cd "$(dirname "$0")/.."
for g in voices/*_glue.c fx/*_glue.c; do
    for api in $(sed -n 's/^#include "\([A-Za-z0-9]*\)Api\.c"/\1/p' "$g"); do
        echo "${api}Api"
        echo "$api"
    done
done | awk '!seen[$0]++'
