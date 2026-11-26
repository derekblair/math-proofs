# The nilpotency-class-six extension

For finite groups of odd order prime to 3 and nilpotency class at most
six, any two nonidentity rim generators give a simple cycle of length
4, 8, 16, 32 or 64 in the single-matching bi-Cayley graph. The local
32-or-64 branch instead assumes the basic commutator in the class-two
quotient has no trivial power among 1, 2, 3 and 4. No claim is made for
all odd-order class-six groups or the full Erdős–Gyárfás conjecture.

The path A=21200212120212020021212120200211 splits into two
same-rim 16-edge paths with labels U,V. B=00212121202002112120021212021202
is its rotation, with label VU. The first half U has zero generator
exponent sums. The product R=UV is a free conjugate of [f,g], where
f=[x,y⁻¹] and g=x⁻¹[y,x²]x. Modulo the third lower-central term,
g=f². Replacing g with g f⁻² does not change [f,g]; it puts the second
argument in the third lower-central term, so R is in the fifth term.

In class six the fifth term commutes with the second term, and
therefore R commutes with U. Consequently UV=VU, and following A
by the reverse of B closes. If R is trivial then A itself closes.
Lean checks the literal free identities; treating a truncated formal
series comparison as an exact group identity is not part of the proof.

The class-two chart separates every same-rim pair of A via gaps at
most four. For the long word the only possible equalities not ruled
out by this chart are (i,i+32) for i=0,1,2,3,4,28,29,30,31.
The label difference is a literal free conjugate of R or R⁻¹ in
each case, so none is equal when R is nontrivial. The chart generator
is untrusted and output checks run in the Lean kernel.

A separate exact C++ check in UT7(F17) uses first superdiagonals
(4,4,4,10,7,1) and (12,12,9,12,2,0), and other above-diagonal
entries zero. A sixth nested commutator of the actual pair has
top-right entry 3, the long word above is simple, and all 98,304
nonbacktracking length-16 half-path endpoints from each root rim
are distinct (likewise at lengths 2, 4, 8). This is an exact
computational sharpness witness, not a Lean-certified exclusion
of the smaller cycles; build the check with g++ -O3 -std=c++17.
