#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
mathlib="$(cd "${1:?usage: verify.sh PATH_TO_PINNED_MATHLIB}" && pwd)"
case "$(git -C "$mathlib" rev-parse HEAD)" in
  d13f23b723b8a846827a245b89c10fc7d3f11612) ;;
  *) echo "Expected the pinned mathlib revision" >&2; exit 1;;
esac
scratch="$(mktemp -d)"
trap 'rm -rf -- "$scratch"' EXIT
cp "$here/"*.lean "$scratch/"
cd "$mathlib"
export LEAN_PATH="$scratch"
lake env lean --version
for module in HaarCycle HaarOrderTwo HaarAllNoncommuting HaarBound16 HaarSharpCore HaarSharpGraph HaarAbelCore HaarAbel HaarCentral HaarClass3Table HaarClass3Collect HaarClass3Cycle HaarClass3Odd; do
  lake env lean --root="$scratch" -o "$scratch/$module.olean" "$scratch/$module.lean"
  printf 'checked %s\n' "$module"
done
