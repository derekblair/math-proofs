# The nilpotency-class-seven extension

For any finite group of odd order not divisible by three and
nilpotency class at most seven, every single-matching bi-Cayley graph
with nonidentity rim generators has a simple cycle of length
4, 8, 16, 32, 64, or 128. More locally, the longer branch only needs
the projected commutator in the class-two quotient to have no
trivial power among 1, 2, 3 and 4. This is not the full
Erdős–Gyárfás conjecture and does not include all odd group orders.

Write gamma_i for the usual filtration starting gamma_1=G. The
32-step word A=12120021212021202002121212020021 splits after 18
steps into U,V, both on the start rim. R=UV lies in gamma_5 and U
in gamma_2. Rotating A gives B with endpoint VU. The endpoint Z
of W = A reverse(B) is the commutator [U,V], lying in gamma_7
because it is conjugate to [U,R]. Thus Z is central in class at
most seven. Rotate W by 27 steps on the same rim; its endpoint
is also Z. The 128-step candidate is W followed by the inverse
of that rotation and closes. If R=1 use A instead. If R≠1 but
Z=1 use W instead.

Simplicity needs more than closure. The class-two chart separates
every pair for A and all but nine pairs for W. For the longest word
it leaves 27 potential collisions: 24 exact free conjugates of
R, Z, or R⁻¹Z, plus (48,98), (49,99), (50,100). If Z≠1 then
R≠1 and R≠Z, since R=Z would imply [U,R]=1. For each of the three
remaining cases the label difference is h⁻¹ modulo gamma_4, where
R is conjugate to [q,h] with q∈gamma_2 and h∈gamma_3. A collision
forces h∈gamma_4, which implies R∈gamma_6 and then Z=1. The
shorter W branch uses the same free comparisons with Z=1.

The group equalities, class-three collection, projected chart, and
all branch glue are formalized. The finite chart generator is
untrusted and only its kernel-checked statements are used. Magnus
computations helped identify the word but no converse from truncated
formal series to group equality is assumed.

A separate exact C++ control in UT8(F17) uses first superdiagonals
(4,4,4,10,7,1,1) and (12,12,9,12,2,0,1), with other upper entries
zero. The selected seventh residue has top-right entry 8 and the
given 128-step word is simple. Both root rims have distinct
nonbacktracking half endpoints up to the checked lengths 2,4,8,16.
This rules out 4,8,16,32 in that instance. A separate explicit
64-step word also closes without repetitions, so the example does
not show sharpness at 128. The matrix check is not Lean.
