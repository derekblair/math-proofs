#!/usr/bin/env bash
# Usage: PATH=/path/to/elan/bin:$PATH ./check.sh /path/to/mathlib4
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
m=$(cd -- "${1:?Provide the prepared Mathlib checkout path}" && pwd)
pin=d13f23b723b8a846827a245b89c10fc7d3f11612
test "$(git -C "$m" rev-parse HEAD)" = "$pin"
tmp=$(mktemp -d)
trap 'rm -rf -- "$tmp"' EXIT
cd "$m"
export LEAN_PATH="$tmp"
lake env lean --version | tee "$tmp/version"
grep -q 'version 4.34.1' "$tmp/version"
for f in WeightedBits Selectors GraphBits Density EdgeBridge Budget Majority ColorBridge Peel Upper Optimum Lower Result; do
    printf '%s\n' "Checking $f"
    lake env lean --root="$src" -o "$tmp/$f.olean" "$src/$f.lean" | tee "$tmp/$f.log"
done
if grep -E "sorryAx|uses .sorry." "$tmp"/*.log; then exit 1; fi
grep -E "^'QuorumMinimum.minSum_order' depends on axioms: \[propext, (Classical\.)?choice, Quot\.sound\]" "$tmp/Result.log"
python3 "$src/control.py"
