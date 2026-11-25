#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean_bin="${LEAN_BIN:-lean}"
"$lean_bin" --version
"$lean_bin" -DwarningAsError=true WowII256.lean
python3 verify256.py
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
sed 's/length = 14 ∧/length = 13 ∧/' WowII256.lean > "$tmp/WrongUnion.lean"
sed 's/def dominating : List (Fin 15) := \[0,1,2\]/def dominating : List (Fin 15) := [0,2]/' WowII256.lean > "$tmp/WrongSet.lean"
for file in WrongUnion WrongSet; do
  if "$lean_bin" -DwarningAsError=true "$tmp/$file.lean" > "$tmp/$file.log" 2>&1; then
    echo "Uncaught negative control: $file" >&2
    exit 1
  fi
  grep -Eq 'decide.*(false|failed)|is false' "$tmp/$file.log"
  echo "Expected rejection: $file"
done
