#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")"
p=${BIKOV_TOOLCHAIN:-$(cd ../.. && pwd)/toolchain}
m="$p/mathlib4"
export LEAN_PATH="$PWD:$m/.lake/build/lib/lean:$(find "$m/.lake/packages" -type d -path '*/.lake/build/lib/lean' | paste -sd ':' -)"
run() { "$p/lean-4.34.1-linux/bin/lean" -M 3000 -o "$1.olean" "$1.lean"; }
if [ "$#" -gt 0 ]; then
  for module in "$@"; do run "$module"; done
else
  while IFS= read -r module; do run "$module"; done < proof-order.txt
fi
