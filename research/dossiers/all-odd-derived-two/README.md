# The sharp 64 bound for odd-order ribbon groups of derived class two

**Theorem.** Let G be finite of odd order. Suppose its commutator subgroup D=[G,G] is nilpotent of class at most two, so [D,D] commutes with D. For any nonidentity x,y in G, the one-matching bi-Cayley graph with rims x and y contains a simple cycle of length 4, 8, 16, 32, or 64. G need not be nilpotent and x,y need not generate G. This removes the exclusion of multiples of 3 from the preceding result.

The Lean entry point is [RibbonAllOddDerivedTwo.lean](RibbonAllOddDerivedTwo.lean), theorem `RibbonAllOddDerivedTwo.finite_odd`. In this graph the vertices are G×{0,1}, the matching edges join equal group labels across rims, and the edges within each rim use x/x⁻¹ or y/y⁻¹. This is not the full Erdős–Gyárfás conjecture. The 64 bound is sharp on the stated class by the [certified class-five UT₆(F₁₇) example](../class-two-bicayley/class-five-sharp/README.md); sharpness on the nonnilpotent subclass alone is not claimed.

## Proof

- The affine field separation step checks all 76 slope branches for odd-order multipliers and handles 2a+1=0 separately. The exceptional profiles reduce to 28 normalized pairs in F7, F11 and F13, with both orientations included. The variant in F43 is discharged directly by a checked word. The field may be an arbitrary finite extension: reported exceptional parameters are values of an embedded prime field, not an assertion that the input field is prime.
- In the stationary group case, bad simple residues from different primes may be mixed. The kernel checks every pair of distinct labels (378 pairs) and every nonzero first-order projective direction (312 directions), and verifies that the precomputed keys used by the checks equal the actual charts. If no pair or tangent is available, the derived subgroup is cyclic and the existing metabelian theorem applies.
- The other missing case is a nontrivial commutator of order 3 in the class-two quotient. A nonzero next graded layer is handled by the short character proof. A stable nonzero third lower-central term instead gives a genuine nontrivial affine residue by an integral cyclic action algebra and Nakayama's lemma. In an exceptional profile, combine its affine chart with the class-two quotient; the rim exponent spans of the chosen words are at most two. All 28 mixed checks certify separation for the source group. A simple cycle is never lifted through an odd cover simply by assuming it stays closed.

An additional [normal-2-kernel corollary](RibbonAllOddTwoKernel.lean) applies whenever G has a finite normal 2-subgroup N and its finite odd quotient satisfies the class-two-derived hypothesis. If neither x nor y squares to 1, there is a simple dyadic cycle of length at most 64 times the exponent of N. This uses the classical [voltage-cover principle](https://doi.org/10.1016/0012-365X(77)90131-5); it does not claim a uniform 64 bound for even-order ambient groups.

[Burkhart's result](https://arxiv.org/abs/2611.05060) concerns ordinary Cayley graphs, whereas the present one-matching [bi-Cayley graphs](https://doi.org/10.1016/j.jctb.2015.10.004) need not be vertex-transitive. No absolute priority is claimed.

## Replay

Use Lean 4.34.1 and Mathlib at `d13f23b723b8a846827a245b89c10fc7d3f11612`. Build or cache the Mathlib imports in `mathlib-imports.txt`, then run `bash replay-local.sh /path/to/mathlib4`. The optional arguments override the sibling predecessor source directories. The script creates a temporary build directory and checks the dependency list in order. All generated certificate inputs are checked by Lean's kernel; no native decision, custom axiom or placeholder is required.
