# A sharp 32 bound for all finite odd-order metabelian groups

A metabelian group is one whose commutator subgroup is abelian. For
every finite metabelian group of odd order, its one-matching
bi-Cayley graph built from any two nonidentity rim generators
contains a simple cycle of length 4, 8, 16 or 32. **Nilpotence is
not assumed.** The earlier exact class-three UT4(F11) example is
itself metabelian, so the bound of 32 is sharp. This is a restricted
family of graphs, not a resolution of the Erdős–Gyárfás conjecture.

The new case is when the rim pair generates a nonabelian metabelian
group but its basic commutator becomes trivial in the class-two
quotient. Writing D for the commutator subgroup, generation then
forces D=[D,G]. View the additive group of D as a module over the
commutative integral group algebra of the abelianization via
conjugation. A simple nonzero quotient is one-dimensional over a
finite residue field K of odd characteristic. The basic commutator
survives in it because it normally generates D. Some group element
s acts by a multiplier μ(s) different from 1 since D=[D,G].

The displacement [g,s] in this quotient supplies an affine
coordinate τ(g). The identity
τ(gh)=τ(g)+μ(g)τ(h) makes (μ,τ) a representation, and on D its
translation coordinate is multiplication by the nonzero
1−μ(s), so the chosen port images do not commute. Swap rims if
needed, move the fixed point of the first port to the origin,
and scale to normalize the two images to (a,0) and (b,1).
Here a≠1 and a,b have odd order.

One of eight explicit 32-edge port words always has distinct
prefix vertices in those affine coordinates. The first word
decomposes every potential same-rim collision into comparisons
of multiplier exponents and an integer Laurent polynomial in the
translation. In the remaining cases b is a fixed power of a
and one of fourteen low-degree polynomials in a vanishes. An
eight-word portfolio covers these cases using 3,374 exact integer
Laurent polynomial certificates. The only needed exceptions
have characteristics 3, 5 and 7; odd torsion rules out the
characteristic-3 and -5 roots that could interfere, and the two
remaining characteristic-7 values are checked with an explicit
finite-field word. The finite tables are proved, not assumed.

**Why the cycle closes in the original group.** Each selected word
has an exact free-group identity as a conjugate of a commutator of
two balanced words. Those two balanced words lie in the actual
derived subgroup and commute in a metabelian group. Thus the
word closes in G. The affine image is used only for separation
of its prefixes, not to lift closure from a quotient.

The field-independent certificate, exceptional finite-field
checks, closure identities, group reduction and final theorem
are fully checked in Lean with standard axioms. The targeted
prior-art search distinguishes [Burkhart's Cayley theorem](https://arxiv.org/abs/2611.05060)
from one-matching graphs in the sense of [Zhou and Feng](https://doi.org/10.1016/j.jctb.2015.10.004).
No absolute priority claim is made.
