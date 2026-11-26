# Exact limits of additive shortcuts for arbitrary planar collinearity

The target remains open: [Alman–Vassilevska Williams, arXiv:2610.06783, §1](https://arxiv.org/html/2610.06783) explicitly leaves the truly subquadratic planar problem open, despite deterministic integer and Las Vegas real subquadratic 3SUM. [Aronov–Ezra–Sharir, SoCG 2020](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SoCG.2020.8) distinguishes restricted geometries and decision-tree results. No improved running time or lower bound for general planar collinearity is claimed here.

## Exact nine-point witness

With rows A, B, C:
- A = [(-3,0), (1,-1), (-2,-3)]
- B = [(3,-3), (2,1), (2,-1)]
- C = [(-1,-1), (0,-3), (0,-2)].

Exactly five unordered triples among the nine points are collinear: the colored index triples 000, 111, 222, 120, 201. In particular 012 is not collinear. Any group labels attached separately to A, B, C (even chosen adaptively from the entire instance) annihilating the five true triples necessarily annihilate 012: the two multisets {000,111,222}, {012,120,201} have the same count separately for each label. Subtract the last two zero sums on the second list. This also applies to an arbitrary fixed target by translating one part, and to multiple conjunctive zero equations by taking the product group.

CollinearityTrade.lean proves this exact obstruction in any additive abelian group, proves the nine points distinct, and exhaustively certifies the full determinant table for all 84 unordered triples. The geometric obstruction is an exact all-triples preservation barrier, not a lower bound on reductions that preserve only the yes/no answer, introduce several disjunctive tags, or attach information to *pairs*. The determinant in fact is the sum of three oriented edge determinants, directly giving Exact Triangle after constructing Θ(n²) weights; that straightforward reduction does not give a truly subquadratic algorithm.

AdditiveLabelCriterion.lean checks the canonical representability criterion in a slightly generalized zero-target form using a free abelian group of incidences and a quotient by all required rows. This common general machinery is already published in the finite fixed-alphabet form in [arXiv:2610.17420 §20.1, Lemma 20.3](https://arxiv.org/html/2610.17420); do not report it as new. The collinearity-specific witness is distinct from that cited theorem; focused search did not establish external priority.

## Coordinatewise collinearity is different and conditionally hard

Encode a first OV bit twice and a second once: A0=(1,0), C0=(2,0),
A1=(0,1), C1=(0,2), B0=(0,0), B1=(3,0). The six points are distinct, and the eight determinants vanish exactly when the A and C bits agree and the repeated bit is not 1 together with the B bit. Applying this per coordinate and taking A and C from separate images of the first OV list forces both positions to use the same vector. Selecting three vectors whose 2D points are collinear in each coordinate is therefore OV-hard for dimension c log n under OVH, by the direct O(nd) construction, also the identification-gadget mechanism of [arXiv:2610.17420 §20.2, Lemma 20.8](https://arxiv.org/html/2610.17420).

CoordinateCollinearity.lean proves the exact existential transfer and shows the product-plane collinearity gap: at A=C bit zero, B0 and B1 require interpolating with parameters −1 and 2 respectively. A line in R^(2d) needs a single parameter for all coordinates. Hence neither this gadget nor its lower bound should be reported for an actual plane or conventional higher-dimensional collinearity.

## Replay and next move

All three Lean modules checked with Lean 4.34.1 against Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612; only standard axioms. Public-only isolated exact Neon XHigh required authentication; no external writes or substitute.

A candidate faster algorithm now needs to exploit pair interaction without materializing all Θ(n²) determinants, or use randomized/structured partial incidences rather than an exact pointwise flattening of the entire tensor. A concrete test is to ask whether partition or sample methods can bound the number of crossing lines induced by one class of compact pair queries *on no-instance inputs*. The universal-label obstruction by itself does not address such an approach.
