# Class-two single-matching bi-Cayley graphs

Let G be a group and let a, b have orders greater than two (possibly infinite).
Take two copies of G. Join g to ga in the first copy, g to gb in the second, and
join each g to its corresponding vertex in the other copy. This yields the
standard simple cubic single-matching bi-Cayley graph
BiCay(G, {a,a⁻¹}, {b,b⁻¹}, {1}). The graph is connected when a and b generate G.

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
