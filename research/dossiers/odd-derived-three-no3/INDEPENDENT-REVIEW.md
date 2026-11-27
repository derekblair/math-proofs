# Independent scope and prior review

The initially failing final log reported unknown D and sorryAx; the current
checked source now names the ordinary commutator group and the fresh final
olean/log report only propext, Classical.choice and Quot.sound. I inspected
the final log and all three concrete premise-supplying modules/logs; no
independent heavy replay. The imported conditional wrapper also prints
standard axioms.

Exact theorem: finite odd G, 3 not dividing |[G,G]|, nilpotency class at
most 3 of [G,G] (third lower-central term with index 0 as the full subgroup),
nonidentity rim steps x,y, and a genuine simple cycle of length one of
4,8,16,32,64,128,256 in the one-matching bi-Cayley graph. There is no
ambient nilpotence or pair-generation assumption and x=y is allowed.
`Ribbon.Cycle` is injective on Fin n and checks all cyclic adjacencies.
Rim edges are same-side right multiplications by the corresponding step
or its inverse, and across sides only equal labels match. For odd finite
G and both steps nonidentity the graph is simple cubic, and it contains
odd rim cycles, so it is not bipartite.

Assembly check: the pair-generated subgroup inherits oddness, both derived
conditions, and the result embeds via pair_lift. In the nonstationary
branch the projected commutator order divides |[G,G]|, excluding 3, with
5 and 7 handled by exact small dispatches and larger by the long local
theorem. In the stationary branch the scalar character kills the
commutator group, so the displacement restricts to an additive
homomorphism there. Characteristic 3 and 3-free derived order imply that
this homomorphism vanishes and contradicts an active normalized chart.
A 3 factor in the ambient order or scalar multiplier order is not
excluded. The widened non-characteristic-three field theorem, pair
cover and jet cover all supply actual checked hypotheses of the same
label bank. No overlooked loophole identified from source.

The earlier coprime-six result (local #80 release replay) requires 3 not
dividing |G| and guarantees at most 128. This is a strict enlargement in
domain with the weaker bound 256; it is not an improvement on the old
bound on its old domain. Neither sharpness nor an unrestricted Erdős–Gyárfás
claim follows.

## Connected strict-domain example

In UT4(F7), put U=I+E12+E34 and V=I+E23 and H=<U,V>.
Let t=diag(2,1,2,1) and G=<H,t>. Matrix conjugation by t sends U→U² and
V→V⁴, so G is a semidirect product H⋊C3 and has odd order divisible by 3.
The first-superdiagonal projection onto the span of (1,0,1) and (0,1,0)
is onto F7². Since H is two-generated, this is its Frattini quotient.
The action of t−1 is invertible on the two eigenspaces, so the image of
[G,G] generates that quotient, hence [G,G]=H by Burnside's basis theorem.
The two vectors (1,1) and (2,4) show the orbit of UV also generates the
Frattini quotient, so the nonidentity ports t and UV generate G. With
commutator convention aba⁻¹b⁻¹, [[U,V],U]=I+2E14, showing H has class
exactly 3 (it lies in UT4). G is not nilpotent, since its Sylow factors would
commute if it were. Independent plain modular-matrix enumeration found
|H|=2401, |G|=7203 and checked the displayed commutator and connected port
generation. The scope separation does not depend on whether the graph
admits an unrelated Cayley realization.

## Public primary comparators

- [Burkhart, arXiv:2611.05060v1](https://arxiv.org/html/2611.05060v1),
  Theorems 1.1 and 1.2: Cayley graphs of odd order or finite nilpotent
  groups (minimum degree at least 3). A semiregular group action with two
  orbits does not establish Cayley graph status. Even for an example
  independently known to be Cayley, Burkhart's stated theorem is existential
  rather than the bounded-length claim above.
- [Tranquilli, arXiv:2608.02675](https://arxiv.org/abs/2608.02675):
  every simple cubic bipartite graph on at most 58 vertices has C4/C8/C16.
  The current graphs have odd rim cycles (unlike Tranquilli's graph
  class), and the connected example has 14,406 vertices.
- No earlier source giving this exact derived-order / class-three /
  unbounded one-matching family was identified in this targeted check.
  This is not an absolute priority, publication-date, or global literature
  claim. The linked remote PR did not render in web search; comparison to
  #80 used the local packaged/replayed theorem.
