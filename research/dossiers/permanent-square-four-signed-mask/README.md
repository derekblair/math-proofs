# Six complex masked determinant squares are necessary at order four even with signed weights

For real variables X of order four, a universal exact sum of fixed entrywise-masked complex determinant absolute squares representing per_4(X^{∘2}) needs at least six summands, even with arbitrary signed real weights. Six suffice by the paired-row construction given below. The same minimum holds for equality on the Boolean cube in this homogeneous masked model. This resolves the signed case expressly left open in [PR #102](https://github.com/derekblair/math-proofs/pull/102). The arbitrary-polynomial SOS ranks in that PR are separate.

## Gram structure with signed weights

Discard zero weights, absorb square roots of absolute weights into the complex matching coefficients c_(j,σ), and denote the remaining weight signs by δ_j∈{±1}. The real row vector v_σ has coordinates (Re c_(j,σ), Im c_(j,σ)) across j. Give the real ambient space the nondegenerate diagonal form of signature determined by the two copies of every δ_j. The signed Gram H has entries Σ_j δ_j Re(c_(j,σ) conj(c_(j,τ))), and diagonal one. If at most five terms are used the dimension is at most 10.

The proof uses the six cosets of V4 in S4, all with four permutations each. The sign parity is constant on each coset, with three even and three odd cosets. Gram entries across cosets are zero because such pairs differ by one nontrivial cycle, and their cross coefficient occurs only once up to reversal. Within each coset all six off-diagonal pairs are linked to pairs in opposite cosets. Every link occurs in a rectangle of two disjoint transposition switches, requiring the sum of its two opposite Gram entries to be zero. For every edge of the K3,3 of cosets there are two rectangles, forming one perfect pairing in each endpoint coset. The three neighbors give the three distinct pairings. For each individual determinant mask the same rectangles satisfy

    c_σ c_(σtu) = c_(σt) c_(σu),
since their edge multisets and permutation sign products agree. All these facts are verified independently in the replay and agree with the coefficient discussion in #102.

Use the nine rectangles below. Each permutation has even incidence, there is one rectangle per edge of the K3,3, and in every coset the three selected opposite pairs form a triangle.

    0123 0132 1023 1032
    0123 0321 2103 2301
    0132 0312 2130 2310
    0213 0231 2013 2031
    0213 0312 1203 1302
    0231 0321 1230 1320
    1023 1320 2013 2310
    1032 1302 2031 2301
    1203 1230 2103 2130

## Rank budget and actual collinearity

A rank-one block with unit diagonal has sign-pair Gram entries. Two unit vectors in a nondegenerate real rank-two space with inner product ±1 are collinear with that real sign: their signed difference is null and lies in the nondegenerate one-dimensional orthogonal complement of the first. This applies to a block after quotienting its span by its radical. A coset with two opposite rank-one neighbors receives ±1 entries on two distinct perfect pairings. These connect the four vertices, so if that coset has rank at most two it must have rank one.

Let (a,b) count rank-one cosets on the even and odd sides. Summing the six block ranks under the total bound ten leaves only (1,1), (1,3), (2,2), (2,3), (3,1), (3,2), (3,3). In (1,1) the four other blocks have rank two. In (2,2), (3,1), and (1,3) the total rank is ten. Case (3,3) is impossible by the odd nine rectangles: link signs multiply to −1 but the incidence product of rank-one vertex signs is +1.

In (3,2) or (2,3), the sole non-rank-one block has all off-diagonal entries ±1, forced by its opposite neighbors. Multiply the sign equations of the nine rectangles. The five rank-one blocks contribute +1 by even incidence. Thus the selected triangle in the remaining block has negative edge product. Right multiplication by the four Klein elements preserves all cosets and is transitive on the missing vertex of that triangle. Applying the same argument to these translates makes all four triangle products negative. Switching vertex signs to make the first row all + then gives −1 on the three remaining off-diagonal positions. Subtracting the first row and column gives a 3×3 block with diagonal zero and off-diagonal −2, of rank three. The original 4×4 block therefore has rank four, and the total rank is nine. This removes the potentially degenerate rank-eight case.

Let W be the coefficient span in the ambient space of dimension D≤10, with radical dimension e. If rank H=t then dim W=t+e and dim W^⊥=D−t−e. Since the radical lies in W^⊥, 2e≤D−t. Every case still possible has t≥9, so e=0. The six coset spans are pairwise orthogonal and individually nondegenerate, since any of their radical vectors would be orthogonal to all of W. In particular the rank-one relations and rank-two collinearities above apply to the actual coefficient vectors and every mask coordinate.

## Eliminate the surviving rank patterns using the masks

Use one observation repeatedly. If two adjacent cosets are rank one, within each every matching coefficient in an individual mask equals its reference coefficient up to a real sign. In a linked rectangle the two sign products are opposite (the linked Gram entries must sum to zero), and the multiplicative identity therefore forces the two reference squares to be negatives of each other. When the set of rank-one cosets on both sides is nonempty, for each mask all even rank-one squares equal a common z² and all odd rank-one squares equal −z².

**One rank-one coset on each side.** All other blocks have rank two and the linked ±1 pairs to an opposite rank-one center are actually collinear. For each mask, start at the even center with square z². The two linked rectangles to each odd coset cover all four of its vertices, and force their squares to be −z² using the same sign argument. Use the odd center to force every even coefficient square to be z². Choose an atom with z≠0, which exists because the even center diagonal is one. Write its coefficients as real signs times z on even cosets and times iz on odd cosets. The multiplicative relation makes the product of the four signs in every rectangle equal −1. The odd nine set contradicts even incidence.

**Three rank-one cosets on one side.** By relabeling suppose all even cosets are rank one and at least one odd center is rank one. For an atom with z=0 every even coefficient is zero, so all six odd pair products in each odd coset are zero. Such an atom cannot contribute to an odd off-diagonal Gram entry. For an atom with z≠0 each odd pair product is ±z². Squaring all six pair products shows that all four squared coefficients in an odd coset equal η_O z² for some η_O∈{±1}. The odd center has η=−1. Write the coefficients as real signs times z or iz according to each coset phase. For a rectangle the sign product equals the phase ratio, which is η_O since the even phase is +1. Multiply over the odd nine rectangles. Even incidence and three uses per odd coset give ∏_O η_O=+1. The two phases apart from the odd center are therefore opposite for this atom. For a chosen odd linked pair with even Gram entry s_E=±1, its bilinear coefficient product is s_E z², so its individual Hermitian real product is s_E η_O |z|². Its required signed Gram entry is −s_E. It follows that Σ_j δ_j η_(O,j)|z_j|²=−1 for every odd coset. Sum the equations for the two noncenter odd cosets. The left side vanishes atom by atom and the right side is −2.

**Two rank-one cosets on each side.** Relabel so the remaining even coset contains 0123 and the remaining odd coset contains 0132. Left translations by an even permutation and conjugation on S4/V4 give this normalization. In every nonzero-center atom the four center cosets have coefficient squares z² or −z² by parity. In each zero-center atom, any pair linked to a known rank-one coset has product zero and contributes no Hermitian real product. For a nonzero-center atom the following cubic relation of squared coefficients comes from identical edge multisets in its two products:

    c_0132² c_0213² c_0321² = c_0123² c_0231² c_0312².
The last two on the left are odd centers and the last two on the right are even centers, so this gives c_0132²=c_0123². Write x=c_0123/z and y=c_0132/z. Both are nonzero because each anchor has a linked pairing to a center. Choose one such linked pair for each anchor. The partner of 0123 has coefficient −s_O z/x, where s_O is its opposite odd center Gram entry, since the bilinear rectangle product is −s_O z². The partner of 0132 has coefficient s_E z/y, where s_E is its opposite even center Gram entry. The two linked equations therefore require respectively

    Σ_j δ_j |z_j|² Re(x_j/conj(x_j)) = +1,
    Σ_j δ_j |z_j|² Re(y_j/conj(y_j)) = −1.
Zero-center atoms contribute zero as above. But y_j²=x_j², so these two left sides are equal, a contradiction.

This eliminates every Gram possibility for at most five terms. On the Boolean cube, every polynomial has a unique multilinear reduction as a function. Each monomial of these homogeneous masked squares has degree two in each raw row. A row of its support containing one variable thus specifies exponent two, and a row containing two variables specifies exponents one and one. Different monomials have distinct multilinear reductions, so Boolean equality implies the same coefficient equations.

## Six masks suffice

Pair rows as {1,2} and {3,4}. For each of the six choices of a two-element column set for the first pair, use its complement for the second pair and put zeros outside the two blocks. In each block, in increasing column order, use mask entries i, 1 in the first row and 1, 1 in the second row, where i is the imaginary unit. If x and y are the two matching monomials of that block, its determinant is ix−y and its absolute square on real variables is x²+y². After a column permutation the full determinant is the signed product of the two block determinants; the sign disappears in the absolute square. Its four squared matching monomials cover exactly the permutations taking the first row pair to the designated column set. The six sets partition the 24 permutations, so summing with weights one gives the target.

## Reproduction and context

Run `node permanent-square-n4-signed-mask-replay.js`. The exact replay verifies all 18 rectangles, the distinct pairings, parity and triangle identities, the cubic support identity, and the rank-budget patterns. It also enumerates 196,608 sign assignments for five rank-one cosets; all 192 compatible assignments force rank four in the sixth block.

Compile `SignedMaskCertificate.lean` with `lake env lean -s 65536 /absolute/path/to/SignedMaskCertificate.lean` under Lean 4.34.1 and Mathlib pinned at `d13f23b723b8a846827a245b89c10fc7d3f11612`. Lean checks the cubic edge-count identity with standard axioms and the finite rank-pattern enumeration without axioms. The indefinite Gram, mask phase, and exact minimum proofs are written, not formalized as a whole.

[Huang et al.](https://arxiv.org/html/2212.12655v2) give related Birkhoff adjacency context. The [Godsil–Gutman estimator](https://onlinelibrary.wiley.com/doi/abs/10.1002/jgt.3190050203) is a randomized determinant-square setting, not this exact finite-sum question. This result does not concern a single affine determinant for the ordinary permanent or an unrestricted permanent algorithm. No priority claim is made.
