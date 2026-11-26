# The 128 bound through nilpotency class eight

For finite groups whose order is coprime to six and whose nilpotency
class is at most eight, each one-matching bi-Cayley graph built from
nonidentity rim generators has a simple cycle of length 4, 8, 16, 32,
64 or 128. This is not a class-eight result for all odd orders or a
solution to the full Erdős–Gyárfás conjecture.

A 32-step word A has residue R in gamma_5. Split A as U,V with U in
gamma_2. Its rotation has label VU. The 64-step word W formed by going
out along A and back along its rotation has residue Z=[U,V] in gamma_7.
Rotating W across the same prefix gives the same group label in class
eight: Z commutes with U, although Z need not be globally central.
The two W words yield the 128-step walk. Use A if R=1 and W if Z=1
but R is nontrivial. In the remaining branch R,Z and R⁻¹Z are
nontrivial because R=Z would force [U,R]=1. Every class-two equality
not eliminated by the small coordinate gaps has an exact free word
certificate as a conjugate of R, Z, R⁻¹Z or their needed inverses.
The finite chart checks cover all three branches.

The basic class-two comparison uses commutator exponent gaps up to 7.
At projected order 5 or 7, three alternative templates give a different
argument. In the class-three quotient the third-layer commutators u and
v are central and have p-th power 1. If none of the three templates
gives a simple dyadic cycle, each forces a different equality
c^p u^a v^b = 1 with exponents taken modulo p. The three (a,b) points
are noncollinear for p=5 and p=7; collecting the equations gives u=v=1.
In the generated group and under nilpotence this makes the third term
vanish. The class-two cycle theorem finishes the contradiction. The
zero projected-commutator case likewise drops to a commuting pair
in the generated subgroup. No analogous completion for order 3 is
claimed here.

All group algebra, exact reduced word checks, finite charts and the
ambient subgroup wrapper are checked in Lean. The generators are
untrusted; their output is checked through exact recurrences and
kernel decisions. No Magnus-series sufficiency is used.

The separate exact UT9(F17) check gives a C128 for 272 parameter pairs
in the tested family, including an explicit pair with nontrivial
eighth commutator. It is a positive check, not an absence census or
a sharpness example.
