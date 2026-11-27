# Power-of-two cycles in odd covers of a doubled square

**Paper theorem.** Start with a square and double two opposite edges. Take a regular cover of that cubic multigraph with finite odd-order voltage group (D) and assume the resulting graph is simple. It contains a simple cycle of power-of-two length in each connected component in any of the following cases (take the voltage-generated deck for that component):

- The deck is nilpotent, or it has a nonabelian prime-power quotient.
- The deck has a primitive affine quotient with cyclic complement of order 3 or 5, with no extra assumptions on the three voltages.
- The deck has a cyclic primitive affine quotient of arbitrary odd complement order where a doubled-edge difference is a nonzero translation and the closing voltage generates the complement modulo translations.

The proof also reduces the remaining nonnilpotent cases to cyclic primitive affine quotients of arbitrary odd complement order. The general square case, the second four-vertex quotient topology, and the unrestricted Erdős–Gyárfás conjecture are not claimed.

## Read and reproduce

- `eg-double-square-odd-deck-frontier.md`: statement, group reductions, case breakdown and exact-certificate proof.
- Run `node eg-double-square-3group-literal-theta.js`, `node eg-double-square-affine-scalar-theta.js`, `node eg-double-square-affine-order3-replay.js`, and `node eg-double-square-affine-order5-replay.js`. The order-3 and order-5 checks cover 90 and 353 literal theta certificates respectively, including all necessary cyclotomic exceptions.
- `BridgeThree.lean`, `CubicAffineSquare.lean`, and `QuinticAffineSquare.lean`: 447 separately kernel-checked path certificates. All are proved with ordinary `decide`, not `native_decide`; no sorry or proof axioms are introduced. A checked Lean chart records valid signed edge walks with shared distinct endpoints, three equal arms, and no other vertex overlap in the indicated coordinate model. The group-theoretic reduction, guard coverage in all characteristics, and odd-deck lifting implications are paper plus exact replay, not a Lean formalization of the whole theorem.
- Lean 4.34.1, Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`. Run `lake env lean -s 65536 <path-to-file>` from that mathlib project.
- The *dihedral lifting* and *long digon chain* notes supply historical local charts used in this proof. The actual short-scalar finite chart bank has 20 remaining normalized labels; an older draft counted 19. The [odd bi-Cayley argument](eg-all-odd-bicayley-main.md) gives the suppression/lifting step and identifies its input seed classifications. The abelian small-orbit theorem and earlier full seed classifications are inputs, not standalone replays provided here.
- [Burkhart’s odd-order Cayley theorem](https://arxiv.org/abs/2611.05060) is related one-orbit prior work. No priority claim is made for these four-orbit cases.
