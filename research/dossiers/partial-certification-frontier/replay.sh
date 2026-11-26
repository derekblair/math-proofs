#!/usr/bin/env bash
set -euo pipefail
d="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
base="$(cd "$d/../.." && pwd)"
m="${MATHLIB_DIR:-$base/emerging/mathlib4}"
L="${LEAN_BIN:-$base/toolchain/lean-4.34.1-linux/bin/lean}"
"$L" --version
git -C "$m" rev-parse HEAD
for dep in "$m"/.lake/packages/*/.lake/build/lib/lean; do
  if [[ -d "$dep" ]]; then DEPS="${DEPS:-}:$dep"; fi
done
export LEAN_PATH="$m/.lake/build/lib/lean${DEPS:-}"
cd "$m"
"$L" --root="$d" "$d/PartialCertification.lean"
"$L" --root="$d" "$d/PartialMDSArithmetic.lean"
python3 "$d/checks.py"
