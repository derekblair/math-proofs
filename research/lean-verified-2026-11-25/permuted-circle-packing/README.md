# Permuted circle packing: Question 5.5 in Lean

For every choice of minimum-cardinality permuted packing of radius-r circles
whose containing square has positive area, the clipped area density tends
to pi/(2 sqrt(3)), approximately 0.9069. This verifies a full limit, stronger
than the requested liminf.

Source question: David Bevan, Cheyne Homberger and Bridget Eileen Tenner,
[Prolific permutations and permuted packings, arXiv:1608.06931 v3,
Definition 3.2 and Question 5.5](https://arxiv.org/pdf/1608.06931v3#page=20).
The printed definition admits size one, but that case clips to a square
of area zero. The two interpretations are explicitly separated:
- `PermCircles.question55_paper`: limit for all minimizing choices with n >= 2,
  using the original [1,n] x [1,n] volume quotient and disks whose interiors
  are pairwise disjoint.
- `PermCircles.singleton_degenerate`: the literal singleton is admissible
  and its square has zero area.
- `PermCircles.minimum_exists`: for every real radius r >= 1, a minimizing
  nondegenerate packing exists.
- `PermCircles.question55`: equivalent result with the board translated by
  (-1,-1).

The proof constructs a near-triangular permutation lattice, then proves a
matching finite packing bound directly using clipped Voronoi cells. It
does not take Thue's bound as an additional axiom. A rank-based count of
the disks near the edge bridges the finite packing bound to the clipped
area in the question. See `proof.md` for the mathematical argument.

## Verification

Lean 4.34.1 and Mathlib v4.34.1
(commit d13f23b723b8a846827a245b89c10fc7d3f11612).
With this Lean toolchain active and the Mathlib checkout and its
dependencies available, run `./Verify.sh /path/to/mathlib`.
The supplied logs record a clean source build and independent Lean kernel
replay of all 23 modules. The final theorems use only `propext`,
`Classical.choice`, and `Quot.sound`.
No native decision axioms or admitted lemmas are used.
