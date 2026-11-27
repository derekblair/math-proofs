# Odd-order one-matching bi-Cayley graphs with 3-free derived subgroup

Let G be finite of odd order. Suppose the derived subgroup [G,G] has
nilpotency class at most three and its order is not divisible by three.
For any nonidentity rim steps x and y, the one-matching bi-Cayley graph
has a simple cycle of length 4, 8, 16, 32, 64, 128, or 256. No condition
on ambient nilpotency is imposed, and three may divide |G|.

[Lean statement](RibbonD3DerivedNoThreeChecked.lean) ·
[Independent scope and prior review](INDEPENDENT-REVIEW.md)

This strictly enlarges the domain of the earlier coprime-six result, but
adds 256 to the list of possible lengths, so it does not improve the
earlier 128 bound where it applies. It is not a proof of the unrestricted
Erdős–Gyárfás conjecture or a sharp bound for this family.

A characteristic-three affine cocycle kills the derived subgroup here:
its scalar part kills the commutators, and the displacement restricted
to the derived subgroup is an additive homomorphism from a group of
order prime to three. It therefore cannot be an active normalized chart.
The order of the projected commutator also divides the derived order,
excluding the order-three branch. The wider residue-field, pair and jet
cover lemmas verify the remaining cases.

With pinned Lean and compiled Mathlib, run the replay script from this
directory. The listed source groups are sibling directories in the
repository. The script checks the Mathlib commit and prepares a clean
artifact directory by default. The root theorem prints its axiom list.

    LEAN_BIN=/path/to/lean bash replay-local.sh /path/to/compiled/mathlib4
