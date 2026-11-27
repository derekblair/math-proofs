# Exact small cases of Frankl's Intersection–Union Product Conjecture

Lean verifies that the largest family on n coordinates with |A∩B| ≥ 2 and
|A∪B| ≤ n−2 for every pair of members, including equal pairs, has the
following sizes:

| n | 9 | 10 | 11 | 12 | 13 |
|--:|--:|---:|---:|---:|---:|
| Maximum size | 50 | 110 | 220 | 484 | 968 |

These exact values are attained by the usual disjoint-block products.
The theorem is IU.intersection_union_9_to_13 in ExactRange.lean. It concerns
the original arbitrary families, not just shifted families or graph cliques.
It settles this specified finite range only. It does not resolve the product
conjecture for general parameters, nor does it address Frankl's unrelated
Union-Closed Sets Conjecture.

## Relation to the literature

[Frankl and Wang, Intersection-union families, JCTA 217 (2026), 106100](https://doi.org/10.1016/j.jcta.2025.106100)
prove the short-excess cases and a large-intersection/union-parameter range.
[Chang, Frankl and Wang, arXiv:2610.25049, Theorem 1.3 (October 2026)](https://arxiv.org/html/2610.25049v1)
prove product optimality for n ≥ 2^15(p+q−2)^3 when both parameters are at
least two. The five listed cases lie outside those stated ranges. This note
does not claim priority or exclude earlier calculation of individual values.

## Proof and verification

1. Simultaneous compression preserves size and the two pairwise bounds.
   A strictly decreasing sum of coordinate labels gives a shifted family.
2. The minimum intersection permitted by the two prefix profiles is the
   maximum prefix excess. Its witness keeps A fixed and selects the earliest
   allowed positions for B, with at most the prescribed number drawn from A.
   One threshold therefore encodes both intersection and union requirements.
3. Explicit proper colorings on the shifted-prefix graphs bound the three odd
   cases. Lean verifies every admissible mask and every within-color pair.
   In the even cases a free extra site doubles the family and transfers the odd
   upper bound. Disjoint-block constructions supply the lower bounds.
4. The separate Python audit uses deadline scheduling, not the Lean prefix
   formula, to verify the saved finite colorings and product-side partition
   maxima. The audit is not trusted by the Lean proof.

To replay, set MATHLIB_DIR to a built Mathlib checkout at commit
d13f23b723b8a846827a245b89c10fc7d3f11612 and run ./replay.sh with Lean 4.34.1
on PATH, or set LEAN_BIN to that pinned executable. The script verifies the
SHA-256 manifest and compiles into a fresh temporary directory. It does not
fetch anything. See proof-order.txt for module order. The final declaration
uses only propext, Classical.choice and Quot.sound; no sorry or native-decide
axiom is involved.
