#!/bin/sh
# The Lean modules that voices/*_glue.c include as inline C, one per line: the Api module, then its base module.
#   tools/glue_modules.sh        e.g. AnalogApi / Analog
cd "$(dirname "$0")/.."
for g in voices/*_glue.c; do
    api=$(sed -n 's/^#include "\([A-Za-z0-9]*\)Api\.c"/\1/p' "$g")
    [ -n "$api" ] && echo "${api}Api" && echo "$api"
done
