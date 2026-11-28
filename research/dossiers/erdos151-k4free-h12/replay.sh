#!/usr/bin/env bash
set -euo pipefail

src="$(cd -- "$(dirname -- "$0")" && pwd)"
: "${LEAN_BIN:?Set an absolute path to the pinned Lean binary}"
: "${MATHLIB_ROOT:?Set an absolute path to the pinned Mathlib checkout}"
build="${REPLAY_BUILD:-$(mktemp -d)}"
mkdir -p "$build"
cd "$build"
build="$PWD"
export LEAN_PATH="$build:$MATHLIB_ROOT/.lake/build/lib/lean:$(find "$MATHLIB_ROOT/.lake/packages" -type d -path '*/.lake/build/lib/lean' | paste -sd:)"
(cd "$src" && sha256sum -c --quiet SHA256SUMS)
count=0
while IFS= read -r m; do
  cp "$src/$m.lean" "$m.lean"
  "$LEAN_BIN" -o "$m.olean" "$m.lean" > "$m.log" 2>&1 || { cat "$m.log"; exit 1; }
  if grep -E 'sorryAx|uses .sorry.|ofReduceBool|Lean.trustCompiler|nativeDecide' "$m.log"; then
    exit 1
  fi
  count=$((count+1))
  printf 'verified %s %s\n' "$count" "$m"
done < "$src/proof-order.txt"
cat H12Final.log
printf 'verified %s source modules\n' "$count"
