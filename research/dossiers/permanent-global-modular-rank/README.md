# Polynomial-space permanent modulo a growing prime power from low global modular rank

**Theorem (written proof).** Let p be prime, A arbitrary integer n×n, r=rank_Fp A>0, and h≥1. Define Λ_p(t,r)=Σ_{j≥1} max(0,ceil((t+r)/p^j)−r) for r≤t≤n. Then there is a deterministic polynomial-bit-workspace algorithm to compute per(A) modulo p^h in time

$$
\operatorname{poly}(n,h,\log p,\text{input bits})\,\binom{n+2r}{2r}\sum_{\substack{0\le q\le n-r\\q+\Lambda_p(n-q,r)<h}}\binom{n-r}{q}2^q.
$$

If the set is empty return zero. At rank zero, per(A) is divisible by p^n; for h>n evaluate per(A/p) mod p^(h−n) by any exact method. No effective rank-zero claim above its vanishing precision.

## Algorithm

Compute Gaussian elimination over F_p and choose r actual basis rows B_j of A (lift the actual integer rows). For every nonbasis row i write A_i=Σ_j u_ij B_j+p C_i with u_ij integer representatives of field coefficients and C_i exact. By multilinearity, expand on correction row sets Q⊂[n−r] of size q, with explicit factor p^q. In the remaining t=n−q rows use the B-row expansion, retaining the r actual basis rows. Group the expansions by multiplicity α of each row type B_j: α_j≥1, |α|=t. The grouped scalar coefficient g_α is [X^α] of the homogeneous degree t polynomial
   G_Q(X)= (∏_j X_j) · ∏_{i nonbasis, i∉Q} (Σ_j u_ij X_j).
For any fixed α, the other factor is the permanent of a matrix with α_j repeats of B_j and all q individual rows C_i (i∈Q). It equals (∏ α_j!) times [X^α ∏_{i∈Q}Y_i] of the degree n polynomial
   F_Q(X,Y)=∏_{ell=1}^n (Σ_j B_{j,ell} X_j + Σ_{i∈Q} C_{i,ell} Y_i).
This follows because the coefficient chooses one row type per column, then the labeled copies of each repeated type can be placed in α_j! ways. Hence the entire Q term vanishes if q+Λ≥h, by the sharp factorial valuation bound. It is valid to skip individual α with q+Σν_p(α_j!)≥h as well. Do not divide by nonunits mod p^h.

## Time and workspace

g_α is obtained by the exact integer mixed forward difference at 0 with orders α, then division by ∏α_j! **in Z** before reduction. The F_Q target already needs that same factorial factor, so take its mixed forward difference directly modulo p^(h−q), with orders α on X and 1 on each Y. Homogeneity matches total difference order, so all other monomials vanish; this is true over any ring. Evaluations require ∏(α_j+1) and 2^q∏(α_j+1) respective grid points. Scan q=0,…,n−r and compute its admissibility inequality before generating any subsets of that size. For admissible q, generate only the q-subsets of nonbasis rows, then the positive compositions α of n−q into r parts, and then the grid points, all by serial bounded-depth iteration. No exponential table is cached. Rank computation, the initial scan, and the empty-sum test cost polynomial time even when every q is excluded. At fixed t the sum of grid counts is ≤[z^t](1−z)^−(2r)=binom(t+2r−1,2r−1)≤binom(n+2r,2r). For integer G_Q evaluation points ≤n and residues u_ij≤p−1, product and difference weights have polynomial bits. For F_Q reduce as operations proceed. Thus storage polynomial and runtime as above. This algorithm combines exact use of modular basis structure with the earlier cleared factorial-forward-difference tool; it is for low global rank mod p, not low ordinary rank or assumed hierarchical geometry.

## Sharp universal valuation bound

If A is an n×n integer matrix and its rank over F_p is r>0, the sharp universal lower bound on ν_p(per A) is

    B_p(n,r) = min_{r≤t≤n} [n−t + Σ_{j≥1} max(0, ceil((t+r)/p^j)−r)].

If r=0 the bound is n. Adopt ν_p(0)=∞. Choose r actual rows as a modular basis and express each remaining row as an integer linear combination of the same lifted rows plus p times an integer row. Expand by multilinearity. A term retaining t lifted basis rows has the explicit factor p^{n−t} and repetition multiplicities m_i≥1 with Σm_i=t. Permuting column assignments inside each group of repeated rows acts freely and preserves weight, so the relevant factorial product divides the permanent. For given t,r, its minimum valuation is the displayed sum. Indeed, for each j the residue per group lies at most p^j−1, giving the stated lower bound on Σ_i floor(m_i/p^j). All bounds can be attained simultaneously: starting from total t, at each base-p digit choose the largest total of r digits in [0,p−1] no greater than the current total with the required residue modulo p. Pass its remaining quotient to the next position. The successive quotient totals are max(0,ceil((t+r)/p^j)−r), by induction. Initially allow zero groups. Whenever a group is zero, moving one unit from a group of size at least two to that group cannot increase the factorial valuation. This reaches positive groups since t≥r and preserves optimality.

The bound is attained by a block diagonal matrix of r all-ones square blocks of sizes m_i and an (n−t)×(n−t) block pI. For a dense positive witness, add p^{B_p(n,r)+1} to each zero entry, with the exponent at least one. The residue mod p and the first nonzero permanent digit stay the same. For rank zero use pI and the same densification. At h=1 the criterion recovers the modular-rank vanishing implication of Yu, revisited by Glynn. [Glynn](https://researchnow.flinders.edu.au/en/publications/the-factorization-of-the-permanent-of-a-matrix-with-minimal-rank-/)

For p=2 and r>0 there is a closed form. Let L=floor(log₂(1+n/r)). Then

    B_2(n,r) = n − rL − floor((n−r(2^L−1))/2^L).

Indeed, Legendre reduces the minimization to maximizing the total binary popcount of r positive sizes with total at most n. A bit of value 2^j can be used at most r times. Taking the cheapest available bits first attains the optimum, includes all r units bits since n≥r, and can be realized by distributing each weight to separate sizes. Using the repeated row bound floor(m_i/2) also gives B_2(n,r)≥ceil((n−r)/2). This gives a deterministic early-zero test before general mod-2^h evaluation.

## Subexponential regime

For fixed odd p, by Legendre and per-row digit sums, Λ_p(t,r)≥ t/(p−1) − r(1+log_p(t/r)). Indeed s_p(m)≤(p−1)(1+log_p m), average via concavity. Thus any surviving q must be smaller than (p−1)/(p−2)·[h−n/(p−1)+r(1+log_p(n/r))]. If r=o(n) and h≤n/(p−1)+O(r(1+log(n/r))), surviving q=O(r(1+log(n/r)))=o(n); the bound is subexponential and polynomial-space, specifically poly · 2^{O(r (1+log(n/r))²)}. For constant r it is quasipolynomial in this sharper precision regime; taking h=n/(p−1)+O(log n) gives a modulus of magnitude p^{Θ(n)}. If h≤n/(p−1)+o(n) same subexponential conclusion when r=o(n); the sharper displayed time uses the actual q bound. For p=2 the inequality loses its q penalty, so do not claim this regime there. The output is one residue of modulus p^h, not Θ(n) guaranteed digits beyond the first nonzero digit of the permanent. If an independent magnitude bound M satisfies 2M<p^h, the signed representative gives exact reconstruction, but this is not an unrestricted exact integer solver.

## Parameterized hardness of removing the n-dependence in the precision parameter
For variable odd prime p, even rank-one mod p matrices with entries in {1,1+pt} are #W[1]-hard for output modulus p^h parameterized alone by h under FPT Turing reductions (the conclusion is no f(h)·poly(n,log p) uniform algorithm unless #W[1] collapses to FPT). This is not a lower bound in the fixed-p, high-h ≈n/(p−1) asymptotic regime above.
Given square binary incidence M of an arbitrary bipartite graph (pad the smaller side with isolated vertices), write m_q for its number of q-matchings. By expanding exactly the q edges selected from M, per(J+zM)=Σ_q z^q(n−q)!m_q, since a chosen q-matching leaves (n−q)! all-ones completions. For p>n query A_t=J+ptM, t=0,…,k, modulo p^(k+1) (h=k+1, rank 1 mod p always). The kth forward difference kills all degrees below k and terms above k vanish modulo p^(k+1). The result is p^k k!(n−k)! m_k modulo p^(k+1). Divide the representative by p^k, invert the two factorials modulo p (units since p>n), and obtain m_k mod p. Take 2k+1 distinct primes >n via separate Bertrand intervals (largest ≤2^(2k+1)·max(n,2), polynomial prime generation in this bound by trial division is FPT). Their product exceeding n^(2k) determines m_k by CRT, as m_k≤n^(2k). Primary #W[1]-hardness of bipartite k-matchings: Curticapean–Marx, https://arxiv.org/abs/1407.2929. No use of ETH lower-bound corollary. This is a rigorous barrier to removing all n-dependent h exponent uniformly in variable p, not an explanation of tightness of the particular q-enumeration bound.

## Reproduction and scope

- `node permanent-global-mod-rank-check.js` compares 100 signed matrices over four primes with independent integer permanent evaluation before reduction, including 70 nonzero outputs and 1,273 skipped correction sets. Its tiny-test enumeration counts skipped sets explicitly; the algorithm above never generates inadmissible sizes.
- `node permanent-global-mod-rank-hardness-check.js` checks the finite-difference residue identity in 80 finite examples. The written reduction, not finite testing, proves the parameterized hardness result.
- `node permanent-prime-power-valuation-witness-replay.js` checks 450 dense positive matrices constructed to attain the bound.
- Run `lake env lean -s 65536 /absolute/path/to/CorrectionRows.lean` from Lean 4.34.1 with Mathlib at `d13f23b723b8a846827a245b89c10fc7d3f11612`. Lean checks the correction-row expansion over commutative semirings. It does not check the sharp valuation, integer divisions, bit complexity, or hardness reduction. The forward-difference identities are separate from this module; see the [hierarchical permanent dossier draft](https://github.com/derekblair/math-proofs/pull/90).

## Supplement: full Smith spectrum

[SmithSpectrum.md](SmithSpectrum.md) proves the exact minimum permanent valuation in a prescribed integer Smith orbit, constructs an attaining representative for each prime, and computes the permanent fixed divisor without factoring. This is a written extension with a [separate exact replay](permanent-smith-valuation-replay.js), not a new Lean claim.

## Related results

[Björklund, Husfeldt, and Lyckberg](https://doi.org/10.1016/j.ipl.2017.04.015) compute permanents modulo prime powers for arbitrary integer matrices without the global rank promise. Their odd-prime speedup applies when hp<n and uses exponential-space tabulation; the present bound instead uses low rank modulo p and polynomial workspace and covers the precision regime stated above. [Glynn](https://researchnow.flinders.edu.au/en/publications/the-factorization-of-the-permanent-of-a-matrix-with-minimal-rank-/) treats modular-rank vanishing and factorization at the critical rank in prime characteristic. [Anwar](https://arxiv.org/html/2611.17812v1) uses rank bounds for full external cuts and endpoint coefficient arrays in prime characteristic. The reduction here uses the bipartite k-matching hardness of [Curticapean and Marx](https://arxiv.org/abs/1407.2929), not an ETH consequence. No priority claim is made.
