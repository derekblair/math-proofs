#!/usr/bin/env bash
set -euo pipefail
if [ "$#" -ne 1 ]; then echo "Usage: $0 /path/to/mathlib4-on-v4.34.1" >&2; exit 2; fi
math="$(cd "$1" && pwd)"
src="$(cd "$(dirname "$0")" && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
mods=(SeparatorLogic SourceBridge Physical ActualPaths Stamps Answer SourceForm)
for m in "${mods[@]}"; do cp "$src/$m.lean" "$work/"; done
export LEAN_PATH="$work:$math/.lake/build/lib/lean:$(find "$math/.lake/packages" -type d -path '*/.lake/build/lib/lean' | paste -sd:)"
cd "$work"
lean --version
printf 'Mathlib commit: '; git -C "$math" rev-parse HEAD
for m in "${mods[@]}"; do
  echo "Compile: $m"
  lean --root="$work" -j1 -o "$m.olean" "$m.lean"
done
for m in "${mods[@]}"; do
  echo "Kernel replay: $m"
  leanchecker -v "$m"
done
