#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
: "${MATHLIB_DIR:?Path to built Mathlib at the pinned revision}"
lib=$(cd "$MATHLIB_DIR" && pwd)
lean=${LEAN_BIN:-lean}
[[ $(git -C "$lib" rev-parse HEAD) == d13f23b723b8a846827a245b89c10fc7d3f11612 ]]
"$lean" --version | grep -F 'version 4.34.1'
(cd "$here" && sha256sum -c SHA256SUMS)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
export LEAN_PATH="$out:$lib/.lake/build/lib/lean:$(find "$lib/.lake/packages" -type d -path '*/.lake/build/lib/lean' | paste -sd ':' -)"
for n in RobustFolkman MixedCorners ParagliderCayley GeometricGraphEdit GeometricMoment GeometricAssembly GeometricWindow GeometricPatterns GramLowOrder GramCoefficients; do
  "$lean" -j1 -M2850 --root="$here" -o "$out/$n.olean" "$here/$n.lean"
done
