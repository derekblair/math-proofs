# Own-harness research — Rule 126 popcount series consolidation (2026-10-27, orchestrator run ~19:53 PDT)

Purpose: one verified index over the finite-evidence popcount tranches, so the
Rule 129 pinfreeze dossier can cite the series as a whole without re-reading
18 tranche reports. This is a consolidation/verification pass over recorded
outputs, not a new computation and not a proof.

## Method
For every tranche directory `~/workspace/math-fleet/lanes/ownharness-rule126-*-20261027/`,
checked its recorded `output.txt` for the terminal markers `ALL CHECKS PASS`
and `TOTAL failures: 0` (grep counts recorded in this run's orchestrator log).

## Result — every popcount tier verified complete in finite-evidence form
- pow2 (popcount 1) and popcount 2 through popcount 18 tranches: each
  `output.txt` contains `ALL CHECKS PASS` and `TOTAL failures: 0`
  (popcount-18 contains both markers twice — sections (A)–(E) run plus the
  (F) bitset run). Supporting tranches mersenne-rows, lucas-submask,
  diagonals, rowcounts also carry `ALL CHECKS PASS`.
- Tranches without those exact terminal markers (a1a4-truthtables, a3lucas,
  closedform, recurrence) are method/support tranches whose own reports do
  not use that marker convention; they are NOT cited as tier evidence here.

## Consolidated statement (finite-evidence form, uniform across tiers)
For popcount p (1 ≤ p ≤ 18), at n = sum of p distinct powers of two with
n ≥ 3·2^(p−1) − 1, the Rule 126 cone row has exactly 2^(p+1) True cells, at
|x| in the union over the 2^(p−1) submasks k of the lower part of
{n − 2k, n − 2k − 1}. Converse verified per tier: count_B = 2^(p+1) iff
popcount(n) = p and n ≠ 2^p − 1, over each tier's recorded converse range
(largest: p = 18, 2 ≤ n ≤ 512000). Sole exception per tier: the Mersenne
n = 2^p − 1, where the row is full (2^(p+1) − 1 cells) and count_S = 0.
Tier thresholds 2, 5, 11, 23, 47, 95, 191, 383, 767, 1535, 3071, 6143,
12287, 24575, 49151, 98303, 196607, 393215 follow x → 2x + 1, i.e.
3·2^(p−1) − 1.

## Status / limits
Finite evidence only; no pinned theorem proved, no Lean invoked. The series
is the p-bit corollary family of the submask criterion, one phenomenon per
tier — the natural stopping point declared at popcount-18 stands. Next step
unchanged: coordinator compile/commit/freeze of the Rule 129 pin per the
pinfreeze dossier §2.3 — a Codex coding step awaiting Derek's explicit lane
confirmation (lane_router gate). No proof lane without the frozen pin.
