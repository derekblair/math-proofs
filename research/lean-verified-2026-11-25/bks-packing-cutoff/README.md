# No constant cutoff for regular permutation pattern packings

For every integer h ≥ 2 there are two admissible pattern-and-overlap choices whose packing counts are equal at each occurrence number j from 1 through h, and unequal at h+1. Consequently no constant finite cutoff works for all patterns, regardless of length.

This strengthens the six-occurrence counterexample to the first question in [Blitvić, Kammoun and Steingrímsson, Part I, §7 item 8](https://arxiv.org/pdf/2610.29846v1#page=48). It does not rule out a bound depending on pattern length. A bounded search found no earlier resolution of the arbitrary-length uniform cutoff.

## Construction

- Fix pattern **1324**, overlap **2**, whose starting positions are two apart. An order of position labels gives a packing if its two rows U and V are separately increasing and U_(t+1) precedes V_t at each window t.
- For each h take a pattern of length 3h+1, step 3 and overlap 3h−2. Name its positions A_i=3i, B_i=3i+1, C_i=3i+2 in zero-based notation. Its values rise in the following position order:
  B_0, …, B_(h−2), A_0, B_(h−1), A_1, …, A_h, C_0, …, C_(h−1).
  Thus a shifted window t enforces all three local row orders, the crossing A_t < B_(t+h−1) < A_(t+1), the placement B_(t+h−2) < A_t, and A_(t+h) < C_t. Here inequalities describe ranks, not positions.
- For j windows, keep A_(h−1), …, A_(h+j−1) and C_0, …, C_j. Their conditions are exactly the U and V conditions of 1324. All omitted early A and late C positions have forced placement. The B positions start with B_0, …, B_(h−2) before A_0; each other B is forced into a specified gap between consecutive A positions.
- If j ≤ h, every B is before A_j, hence before A_h, hence before C_0. All comparisons involving an omitted position are determined, so restriction and extension give a bijection between packings.
- At j=h+1 the last B goes between A_h and A_(h+1). The canonical extension places each B just before its right-hand A neighbour. This still gives an injection. Choose any permitted U/V order with U_1 < V_0 < U_2, for example U_0, U_1, V_0, U_2, …, U_j, V_1, …, V_j. In the larger pattern, C_0 lies between A_h and A_(h+1), so the last B can instead go before C_0. This second placement restricts to the same small packing and is outside the canonical image. Thus the big pattern has strictly more packings at h+1.

For h=5, the second pattern is 5, 1, 12, 7, 2, 13, 8, 3, 14, 9, 4, 15, 10, 6, 16, 11 with overlap 13. Both counts start 1, 2, 5, 14, 42; the sixth counts are 132 and 174.

## Formal scope and verification

Lean theorems: `CoverCutoff.arbitrary_delay` and `CoverCutoff.no_uniform_cutoff`, in `ArbitraryCutoff.lean`. Counts are of actual permutations obeying every strict comparison in each required consecutive window, with additional occurrences permitted. The proof checks that both overlaps are admissible and that each step is at least two.

The uniform proof uses comparison-preserving constructions and finite cardinality, not extrapolation from a search or a Catalan formula. The separate independent Python check enumerates the finite example using the full window comparisons and tests the row model.

With Lean 4.34.1 and Mathlib v4.34.1 commit `d13f23b723b8a846827a245b89c10fc7d3f11612`, run:

```bash
./VerifyUniform.sh /path/to/mathlib4 /path/to/new-verification
```

This builds every module from source, checks the axiom footprint, replays the modules with the kernel, and repeats the independent arithmetic checks.
