# Additive-square detection with a unit eigenvalue
For a finite integer alphabet D, consider a prolongable substitution f whose
iterates grow unboundedly. Suppose the length and sum of each letter image are
obtained by applying a fixed integral 2-by-2 matrix A to (1,x), for x in D.
The executable Boolean in [NeutralAffineExact.lean](NeutralAffineExact.lean)
decides whether the limit word contains a pair of consecutive nonempty blocks
of equal length and sum, when A has one eigenvalue +1 or -1 and a second
eigenvalue of absolute value greater than one. Image lengths need not be uniform.
The main theorem is `NeutralAffineExact.calculate_correct`. Its right-hand side
uses an exact additive-square factor in some finite iterate. Prolongability and
unbounded growth identify these factors with those in the infinite prefix limit.

Three cuts are tracked by the letters immediately after them, their offset choices,
and flags for strict order. Their prefix-signature second difference evolves by
A plus a finite stamp. Integer left eigenvectors are computed from A. The expanding
coordinate of every accepting path stays bounded by a backwards recurrence.
For the neutral coordinate a sign bit removes the multiplication by ±1; exact
acceptance is then a zero-total signed path in a finite indexed graph. The
verified graph algorithm subdivides arbitrary signed weights into private chains
and uses balanced-walk saturation. Zero-weight edges are not erased. The finite
graph construction and both directions of the word correspondence are checked.
A worked example with reachable rules of lengths 2, 3, and 4 is in [NeutralReachable.lean](NeutralReachable.lean).

## Scope and related work
- [Currie, Mol, Rampersad and Shallit](https://arxiv.org/html/2111.07857)
  and [Andrade and Mol, Theorem 2.4](https://arxiv.org/html/2408.15390v2#S2.SS4)
  give criteria with both eigenvalues of the projected affine matrix expansive.
- [Rao and Rosenfeld](https://arxiv.org/abs/1511.05875) use a different
  criterion on the full incidence matrix, excluding unit-modulus eigenvalues.
- This dossier covers only the stated spectral regime and additive squares.
  It does not settle the minimum alphabet in
  [Shallit §8](https://arxiv.org/html/2611.24441v1#S8), handle arbitrary k,
  claim unconditional priority, or give a practical complexity bound.
  The Boolean is an executable reference decision procedure, not a benchmarked
  implementation. Bounded mathematical toys and conjecture counts are not claimed.

## Reproduction
Use Lean 4.34.1 and mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612` with its dependencies built.
Run `bash verify.sh /path/to/mathlib4` to check the files in a clean temporary
module directory. No default build targets are modified.
