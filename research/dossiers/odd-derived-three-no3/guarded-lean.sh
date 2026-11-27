#!/usr/bin/env bash
set -euo pipefail
lean=${D3_LEAN_BIN:?Set D3_LEAN_BIN to Lean 4.34.1}
if [[ ${1:-} == --version ]]; then exec "$lean" "$@"; fi
cap=4350; gate=6000
case "${*: -1}" in
  *RibbonD3WidePairCheck*.lean|*RibbonD3PairCheck*.lean|*RibbonD3WidePairJetCover.lean|*RibbonD3WideJetCheck*.lean|*RibbonD3JetCheck*.lean|*RibbonD3WidePairJet.lean|*RibbonD3DerivedNoThreeChecked.lean)
    cap=5900; gate=6700 ;;
esac
for wait in $(seq 1 240); do
  mem=$(awk '/^MemAvailable:/{print $2}' /proc/meminfo)
  if ((mem>=gate*1024)); then exec "$lean" -j1 -M "$cap" "$@"; fi
  sleep 5
done
exit 75
