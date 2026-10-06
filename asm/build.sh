#!/bin/sh
# Usage: sh build.sh [input] [render]
#   input  : 14-character cube state (default 21345671111111)
#   render : 0 = CLI build without the LED renderer (default), 1 = GUI build
# Output: build/solver.s, one file for the Ripes assembler.
set -e
INPUT=${1:-21345671111111}
RENDER=${2:-0}
mkdir -p build
{
    cat tables.s
    if [ "$RENDER" = 1 ]; then
        cat solver.s
    else
        # drop everything between "# RENDER_BEGIN" and "# RENDER_END"
        sed '/# RENDER_BEGIN/,/# RENDER_END/d' solver.s
    fi
} | sed "s/@INPUT@/$INPUT/" > build/solver.s
echo "built build/solver.s (input $INPUT, render $RENDER)"