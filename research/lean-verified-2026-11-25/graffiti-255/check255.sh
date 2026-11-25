#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean_bin="${LEAN_BIN:-lean}"
"$lean_bin" --version
"$lean_bin" -DwarningAsError=true WowII255.lean
python3 verify255.py
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
sed 's/i-3 == j-7/false/' WowII255.lean > "$tmp/WithoutMatching.lean"
sed 's/maxEdgeNbr 11 graph = 7/maxEdgeNbr 11 graph = 6/' WowII255.lean > "$tmp/WrongMaximum.lean"
for file in WithoutMatching WrongMaximum; do
  if "$lean_bin" -DwarningAsError=true "$tmp/$file.lean" > "$tmp/$file.log" 2>&1; then
    echo "Uncaught negative control: $file" >&2
    exit 1
  fi
  grep -Eq 'decide.*(false|failed)|is false' "$tmp/$file.log"
  echo "Expected rejection: $file"
done
