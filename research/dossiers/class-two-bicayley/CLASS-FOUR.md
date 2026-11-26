# Sharp class-four single-matching bi-Cayley result
This lane builds on the class-two and class-three ribbon results, not the
multiplication graph with all three edges crossing its two sides.

**Best upper proof:** RibbonClass4Family.involution_free_class4 proves a simple C4, C8, C16, or C32 in the cubic single-matching bi-Cayley graph for every group of nilpotency class at most four with no involutions, including infinite groups. It applies in particular to every finite odd-order group of that class, including characteristic three. RibbonClass4Family.cycle32_of_fourth needs only a selected fourth-layer commutator whose fourth power is not the identity, even in a group with other torsion. Its projection estimate shows that this forces nontrivial fourth power of the commutator image modulo LS₂ (= gamma₃); the short mixed template only needs that local condition. When all fourth-layer coordinates vanish in the generated subgroup, the group drops to class at most three, proved via quotient by its center.

The word is `12002002121121200200211212002121`, where 0, 1, 2 denote forward
rim, reverse rim, spoke. The Hall collector checks closure after 20 rim
edges and 12 spokes; same-side pairs with equal rim exponents have
c-coordinate differences of magnitudes precisely 2 or 4. In addition, the
whole exponent trace has span two in each rim. Hence projected conjugation
signatures certify simplicity. The mixed word's first nonzero integral
Magnus coefficient occurs in degree 5 (`ababb` is −4); it is not a class-five
law. The finite degree-five observation about this fixed word is computational, not a formal claim about class-five graphs.

**Auxiliary exact C64:** `RibbonClass4.cycle64_of_fourth` gives a simple C64
when one selected fourth commutator is not of order 1, 2, or 3, with no
finiteness hypothesis. `target_power_from_proj` shows if the projected
commutator's n-th power is one, the selected fourth commutator's n-th power
is one. The independent 64-edge templates are useful for cycle-spectrum
information but do not determine sharp dyadic onset in this class.

**Exact-class-four sharpness:** `RibbonClass4SharpGraph.class_exact` and
`.sharp` use explicit UT5(F11), with x=(1,0,1,1), y=(0,1,1,1) on first
superdiagonal and zeros elsewhere above it. This has no C4, C8 or C16, and
does have C32. The connected root component inherits precisely the same cycle spectrum, verified by RibbonClass4SharpGraph.connected_sharp. No connectivity assertion is made for the whole ribbon over the ambient group. Rooted
nonbacktracking half-word endpoints are certified by kernel-verified owner
hashes; equality of actual endpoints always implies equal owner, so the
checker trusts no probabilistic collision hypothesis or external result.

Replay via bash replay-local.sh /path/to/built/mathlib4 with pinned Lean 4.34.1 and the sibling Haar sources. Regenerate the mask certificate with python3 upper5.py > owner5.txt followed by python3 gen_sharp_cert.py. Only standard axioms: propext, Classical.choice, Quot.sound. See CLASS-FOUR-AUDIT.md for independent review.
