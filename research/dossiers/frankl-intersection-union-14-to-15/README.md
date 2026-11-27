# Exact n=14 and n=15 cases of Frankl's Intersection–Union Product Conjecture

This is a source extension of the separately verified n=9–13 bundle. It
checks the following exact maxima in the original problem, with p=q=2:

| Ground-set size | 14 | 15 |
| --- | ---: | ---: |
| Largest family | 2046 | 4092 |

For every pair of members (including equal members), the intersection must have
size at least 2 and the union must have size at most n−2. The code concerns
arbitrary finite families of subsets, not only compressed families. The final
Lean declarations are IU.IU15Tree.exact14 and IU.IU15Tree.exact15 in
Exact15.lean. This extension covers exactly those two cases, makes no claim of
priority, and does not solve the full conjecture.

## Proof

1. The previous bundle's compression puts the problem in a graph of prefix
   profiles. Compatible profiles can be paired when their largest prefix
   excess meets a threshold fixed by their cardinalities.
2. A 4092-vertex anchor is the usual product: at least four points in a
   six-element left block, at most three in an eight-element right block,
   and one free coordinate. Fix a proper auxiliary coloring of the entire
   graph into 4106 colors. The coloring need not be optimal.
3. A clique of more than 4092 vertices cannot contain a vertex whose surviving
   neighbors meet at most 4091 colors. In two rounds all vertices outside
   the anchor are eliminated. At a fixed weight, checking only maximal
   prefix profiles is sufficient, provided the maximal labels themselves
   are eliminated first within each round. The proof checks 36 omission
   rows (15 missing colors each) and never assumes the 4106 coloring is
   itself the claimed bound.
4. Exact Hamming-weight and prefix-threshold bitmasks certify that the
   auxiliary coloring includes every admissible profile, with no native
   proof axiom. Adjoining a free site doubles any n=14 family and gives
   the n=14 upper bound. The balanced block products attain both values.
5. The optional Python certificate checker verifies the supplied data by
   deadline scheduling, not by the Lean prefix maximum formula. It plays
   no trusted role in the proof.

## Reproduce

Set BASE_SOURCE_DIR to the verified n=9–13 bundle (kept unchanged), MATHLIB_DIR
to a built Mathlib checkout at d13f23b723b8a846827a245b89c10fc7d3f11612, and
optionally set LEAN_BIN to the pinned Lean 4.34.1 executable. Run ./replay.sh.
Both source manifests are checked, and all modules are replayed into a fresh
temporary directory. Script uses no downloads. See proof-order.txt for the
extension module order. The final exact statements use only propext,
Classical.choice and Quot.sound.

[Frankl–Wang, JCTA 217 (2026), 106100](https://doi.org/10.1016/j.jcta.2025.106100)
cover the small-excess and large-parameter ranges.
[Chang–Frankl–Wang, arXiv:2610.25049, Thm 1.3](https://arxiv.org/html/2610.25049v1)
give the large-n result n ≥ 2^15(p+q−2)^3; it does not cover n=14 or n=15
for p=q=2. The claim here is the precise finite theorem and its replay.
