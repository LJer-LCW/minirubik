#!/bin/sh
# Usage: sh build.sh [input] [render]
#   render = 0 (default): CLI build, no LED code and no LED tables
#   render = 1          : GUI build with the LED renderer and its tables
set -e
INPUT=${1:-21345671111111}
RENDER=${2:-0}
mkdir -p build
{
    cat tables.s
    if [ "$RENDER" = 1 ]; then
        cat render_tables.s
        cat solver.s
    else
        sed '/# RENDER_BEGIN/,/# RENDER_END/d' solver.s
    fi
} | sed "s/@INPUT@/$INPUT/" > build/solver.s
echo "built build/solver.s (input $INPUT, render $RENDER)"
