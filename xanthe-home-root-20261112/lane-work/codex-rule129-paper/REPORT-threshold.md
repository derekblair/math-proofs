# Own-harness tranche — Rule 126 popcount threshold sharpness (2026-10-27, ~20:23 PDT run)

Stream 3/3 (Bossman's own harness). Script: `compute.py`. Recorded output:
`output.txt` (exit 0, TOTAL failures: 0, ALL CHECKS PASS). Pure Python +
numpy, no Lean invoked. Finite evidence only; no pinned theorem proved.

## Question
The popcount tranches p = 1..18 (consolidated 2026-10-27 ~19:53) each
state the tier result for n ≥ T_p = 3·2^(p−1) − 1 and treat the Mersenne
n = 2^p − 1 as the sole exception. No tranche isolated whether T_p is
sharp — what p-bit cases, if any, sit below T_p and fail, and how.

## Finding (stronger than the question)
**There are no p-bit integers strictly between the Mersenne exception
and the threshold.** T_p is the second-smallest p-bit integer: the
smallest is 2^p − 1 (bits 0..p−1), the second is (2^(p−1) − 1) + 2^p =
T_p (bits 0..p−2 plus bit p). So at the low end the tranches' hypothesis
"popcount(n) = p and n ≥ T_p" is exactly "popcount(n) = p and n is not
the Mersenne exception" — the threshold is sharp by the ordering of
p-bit integers themselves, not by a union defect accumulating below it.

## Evidence recorded in output.txt
- (S2) For every p in 1..18, the complete list of p-bit sums with bits
  in 0..p (p+1 values; complete for every n < 2^(p+1), hence for the
  whole interval) is printed; exactly two are ≤ T_p — 2^p − 1 and T_p —
  and none lies in between. Any p-bit n with a bit ≥ p+1 exceeds
  2^(p+1) > T_p trivially, so the enumeration covers all candidates.
  Cross-consistency: the p = 18 list (19 values ≤ 524288) is exactly
  the popcount-18 tranche's generation list.
- (S1) At n = T_p for every p: the candidate |x| union U over the
  2^(p−1) lower-part submasks has exactly 2^p distinct values, all ≥ 1
  (minimum value 2^(p−1)), no collisions, and count_B (direct symmetry
  count; pinned math.comb B for n ≤ 1000) equals the tier count 2^(p+1).
- (S3) At the Mersenne n = 2^p − 1 for every p: U produces 0 exactly
  once (k = lower part itself gives n − 2k − 1 = 0), |U| = 2^p distinct
  values, count_B = 2^(p+1) − 1 — the x=0 single-cell mechanism behind
  the tranches' section-(E) exception, verified uniformly here.
- (S4) At every enumerated n the smallest produced value is
  n − 2·kmax − 1 with kmax = the lower part of n (identity checked).

## Honest deviation note
The tranche's first draft expected several below-threshold generations
exhibiting union defects (non-positive values / collisions) and checked
for them; the enumeration refuted that expectation — the interval is
empty and the defect branch never fires. The script and this report
were revised to record the finding as found (S2 in its strong form);
the vacuous defect check remains in the code as a guard.

## What this does NOT show
Nothing about p-bit n above T_p (the tranches' own ranges cover that),
nothing for popcount > 18, and no Lean statement. It sharpens the
finite-evidence statement the pinfreeze dossier cites: the consolidated
series may phrase its hypothesis as "popcount(n) = p, n ≠ 2^p − 1"
at the low end without a hidden gap between the exception and T_p.
Next step unchanged: coordinator compile/commit/freeze of the Rule 129
pin per the pinfreeze dossier §2.3 — a Codex coding step awaiting
Derek's explicit lane confirmation (lane_router gate). No proof lane
without the frozen pin.
