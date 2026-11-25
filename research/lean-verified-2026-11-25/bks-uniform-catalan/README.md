# Uniform Catalan representatives for prescribed pattern packings

This answers the Catalan part of item 6 in §7 of Blitvić, Kammoun, and Steingrímsson, [Permutations, Pattern Covers, Posets and Positivity, Part I](https://arxiv.org/pdf/2610.29846v1). For every overlap m>2 and length K>2m, one explicitly given K-pattern yields precisely the j-th Catalan number of prescribed packings for every j>=1. A prescribed packing is a permutation in which all windows starting step K-m apart have the specified pattern; other occurrences are not forbidden. The same construction works at K=2m too. The top theorem proved for the requested strict range is FussCover.uniform_catalan_pattern in CatalanAnswer.lean.

Zoltán Nagy [arXiv:2611.06937](https://arxiv.org/abs/2611.06937) previously answered the distinct double-factorial part of the question. The authors' [Part II, §7.3](https://arxiv.org/pdf/2611.12829) lists several earlier Catalan and Fuss–Catalan special cases. This Lean bundle makes no novelty claim for those special cases and does not prove a general Fuss–Catalan extension.

## Explicit pattern
Put z=m−2, h=K−2m and F=2z+h, and here write permutation values as ranks numbered 0 to K−1. Concatenate three lists:
- prefix: 0 through z−1, then F+1 and F+3;
- private slots: z through z+h−1;
- suffix: z+h through F−1, then F and F+2.
In one-based notation the m=3, K=7 pattern is 1572346. The prefix and suffix both increase, so the overlap is admissible.

## Why the count is Catalan
Every occurrence has two pairs of active points, A and B at its prefix and the next copy's A and B at its suffix. The remaining positions form one forced head chain below all active points. At time t the active order is A(t+1)<A(t)<B(t+1)<B(t). Reverse time and remove the compulsory first A and final B. Packings are now interleavings of two chains of j points, with the i-th A before the i-th B. Marking the A's as up-steps and B's as down-steps gives a Dyck word; the Lean proof constructs both directions, preserves all original window comparisons, and applies the Mathlib count of Dyck words.

## Reproduction
Run ./verify.sh with a built Mathlib v4.34.1 checkout. Lean 4.34.1 and leanchecker must be on PATH. If the checkout lacks the DyckWord and Fin.Tuple.Take artifacts, build Mathlib.Combinatorics.Enumerative.DyckWord and Mathlib.Data.Fin.Tuple.Take first. The script recompiles the source in a fresh directory and independently replays each project module.
