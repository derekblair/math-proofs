# Exact delay for equal-width permutation packings

**Main formal statement:** `CoverCutoff.equal_width_exact_delay`, in `ExactEqualWidth.lean`.

For each integer h ≥ 2, there are two admissible patterns of length 3h+1 with the same overlap 3h−2. Their prescribed consecutive-window packing counts agree at every positive number of occurrences through h. At h+1 the larger count exceeds the smaller by exactly the h-th Catalan number. In particular, any cutoff that decides all such comparisons at this length and overlap must be at least h+1.

This strengthens the length-independent counterexample to Section 7, item 8 of Blitvić–Kammoun–Steingrímsson, [arXiv:2610.29846v1](https://arxiv.org/abs/2610.29846v1). It does not answer whether a cutoff depending on the pattern length exists. No earlier statement of this exact equal-width refinement was located in the original paper, Part II, or the checked sources; this is not an exhaustive priority claim.

The original window constraints reduce to ordered rows. At j=h+1 the delayed pattern has one extra binary choice exactly when U1<V0<U2 in its reduced order. Such restricted orders correspond bijectively to Dyck words of semilength h, so each contributes one extra packing. The comparator returns exactly the reduced order count, for all positive j.

**Rebuild:** supply a Mathlib v4.34.1 checkout at commit d13f23b723b8a846827a245b89c10fc7d3f11612. With Lean v4.34.1, Lake and leanchecker on PATH, run `bash verify.sh /path/to/mathlib4 verification`. The verifier compiles 18 new source modules and 22 dependencies already in the previous research drop in a clean temporary directory, and replays each with leanchecker. The 40-module clean check passed under the pinned toolchain before submission. The independent Python test enumerates linear extensions of actual window orders for small instances; it is not part of the proof.
