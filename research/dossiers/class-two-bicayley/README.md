# Class-two single-matching bi-Cayley graphs

Let G be a group and let a, b have orders greater than two (possibly infinite).
Take two copies of G. Join g to ga in the first copy, g to gb in the second, and
join each g to its corresponding vertex in the other copy. This yields the
standard simple cubic single-matching bi-Cayley graph
BiCay(G, {a,a⁻¹}, {b,b⁻¹}, {1}). The graph is connected when a and b generate G.

## Class-five extension

[The class-five theorem](CLASS-FIVE.md) gives a 64 upper bound on the first dyadic cycle for finite groups of odd order not divisible by three. Its two linked words give a 32- or 64-cycle under the local quotient hypothesis. The exact class-five lower-bound example is computational, not fully Lean-verified yet.

## Class-four extension

[The class-four result](CLASS-FOUR.md) keeps the same sharp 32 upper bound for groups of nilpotency class at most four with no involutions, including all finite odd-order groups. An explicit connected example from the exact class-four case has C32 and no C4, C8 or C16. The new short template uses consecutive rim edges as well as matching edges, rather than alternating at every step.

## Class-three extension

[The class-three follow-up](CLASS-THREE.md) proves a simple C4, C8, C16 or C32 for the same cubic construction over any group of nilpotency class at most three with no elements of order two, including infinite groups. In the class-three branch a selected triple commutator whose square differs from the identity forces C32 directly. An explicit connected example has C32 and no C4/C8/C16, so 32 is sharp. This is not a proof of the full Erdős–Gyárfás conjecture.

## Class-two theorem

**Lean theorem.** If ab=bac and c commutes with a and b, this graph has a simple
cycle of length 4, 8 or 16. Neither group finiteness nor odd-order assumptions
are needed. The actual Lean hypotheses are a≠1 and b²≠1, so it also applies to
some noncubic instances. Replay: `bash replay-local.sh /path/to/built/mathlib4`.
`Ribbon.class2_pair` and `RibbonSharp.sharp` have only the standard Lean axioms.

When c=1, use the usual two-rim 8-cycle by duplicating each label of the commuting
rectangle 1,a,ab,b across the two rims. If corners collide (a=b or ab=1), the rims
share an edge, giving a 4-cycle. When c≠1, use alternating rim steps
a,b,a⁻¹,b⁻¹,a,b⁻¹,a⁻¹,b, placing one spoke between consecutive steps, including the
closing seam. The eight group labels, in order, are
1,a,bac,bc,c,ac,b⁻¹a,b⁻¹. Conjugation by a or b recovers the respective small
exponents modulo the order of c. For c²≠1, the only remaining equal signatures
are separated by different c-exponents. If c²=1, the only new collision requires
b²c=1, which forces a 4-cycle along the b-rim; otherwise the 16-cycle is simple.
`RibbonSharp.sharp` verifies sharpness on the explicit order-27 triangular group
over F3 by a kernel-checked port-word census and the structural 16-cycle proof.
`check_sharp.py` is a separate exact Python checker.

The standard terminology/model is discussed in Conder, Zhou, Feng and Zhang,
*The automorphisms of bi-Cayley graphs*, JCTB, https://doi.org/10.1016/j.jctb.2015.10.004.
Cyclic generalized Petersen and I-graph 8-cycle constructions are prior art;
see *Distinguishing graphs via cycles*, https://www.sciencedirect.com/science/article/abs/pii/S0166218X24005092.
Ghaffari and Mostaghim, *Erdős–Gyárfás conjecture for some families of Cayley
graphs*, Aequationes Mathematicae 92 (2018), 1–6, §2.4, Theorem 2.4,
https://link.springer.com/article/10.1007/s00010-017-0518-3, already use exactly
the above eight-letter closed word in ordinary Cayley graphs over groups of
order p³. The closed word is not new. The argument here concerns the layered
construction, uses different collision behavior (16 graph edges and a
separate 4-cycle degeneration), and imposes only local class-two assumptions
on the pair. Burkhart, https://arxiv.org/abs/2611.05060, covers ordinary Cayley
graphs of finite odd-order and finite nilpotent groups but not arbitrary
bi-Cayley graphs, which need not be vertex-transitive. No absolute priority claim.

`class3_next.py` is exploratory only: 224 alternating unit-rim patterns give
simple degree-3 Magnus traces but all have degree-2 prefix collisions. A
class-three theorem cannot simply transfer their separation from the class-two
quotient. Different lengths, mixed run lengths, or class-three separation proofs
remain open. The full Erdős–Gyárfás conjecture is not settled here.

For a witness genuinely outside ordinary Cayley graphs, take the same triangular
group times C5, with a=(x,0) and b=(y,1). The two rim generators have orders 3 and
15. The graph is connected, has 270 vertices, has a triangle at the identity
on the a-rim but no triangle at the identity on the b-rim, and consequently is
not vertex-transitive. `RibbonAsymm.lean` formalizes this control and checks
sharpness; independent direct graph census: `python check_asymm.py`.

## Class-six extension

See [CLASS-SIX.md](CLASS-SIX.md) for the class-six 64 bound when group
order is coprime to 6, the independent proof audit and the scope of the
separate exact computational sharpness witness.

## Class-seven extension

See [CLASS-SEVEN.md](CLASS-SEVEN.md) for the Lean 128 upper bound
through class seven, the exceptional quotient comparisons, and the
scope of the separate exact example. This does not claim sharpness
at 128.

## All odd orders through class five

[RibbonP3Odd.lean](RibbonP3Odd.lean) removes the earlier exclusion
of 3 from the class-five theorem. The [character proof](CLASS-FIVE-ORDER-THREE.md)
selects one of two short pairs of port words. The same restriction is lifted for class six below; it remains for
the class-seven bound.


## All odd orders through class six

[Ribbon6Odd.lean](Ribbon6Odd.lean) gives the class-six 64 bound for
every odd group order. [The order-three proof](CLASS-SIX-ORDER-THREE.md)
uses the same class-six port words and reverses one rim direction for
three of the nine character choices.

## No bound on ambient nilpotency class

[DERIVED-SUBGROUP.md](DERIVED-SUBGROUP.md) describes two results
for finite odd-order nilpotent groups without a class cap. The bound
is a sharp 32 when the derived subgroup is abelian, and an upper bound
of 64 when the derived subgroup has nilpotency class at most two.
See [RibbonMetaHeadline.lean](RibbonMetaHeadline.lean) and the independent
audit. These results are for one-matching bi-Cayley graphs, not the
full open conjecture.

## Class eight for orders coprime to six

[CLASS-EIGHT.md](CLASS-EIGHT.md) gives the Lean 128 upper bound through
class eight, including explicit proofs for projected commutator orders
5 and 7. Order divisible by 3 remains excluded for this class.

## All finite odd-order metabelian groups, not just nilpotent groups

[ALL-ODD-METABELIAN.md](ALL-ODD-METABELIAN.md) gives the sharp 32
bound with no nilpotence assumption. The group-structure reduction,
all affine alphabet cases, and actual closing identities are Lean
verified in [RibbonAffineFinal.lean](RibbonAffineFinal.lean).

[NONNIL-SHARP.md](NONNIL-SHARP.md) strengthens the sharpness result:
a connected example remains sharp at 32 even within the nonnilpotent
subfamily. It projects onto the affine group of order 21. The check
excludes C4, C8, and C16, not every shorter cycle length.

The [class-five sharp example](class-five-sharp/README.md) now has a
full Lean certificate, including the exclusion of the four smaller
power-of-two lengths. It uses an optional longer replay separate from
the upper-bound theorems.
