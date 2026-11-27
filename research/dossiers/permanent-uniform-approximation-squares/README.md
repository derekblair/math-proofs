# A polynomial square-length approximation for the entrywise-squared permanent

Let \(P(X)=\operatorname{per}(X^{\circ2})\). For \(0<\varepsilon<1\), let \(L_\varepsilon(n)\) be the minimum \(r\) for which some real polynomials \(q_1,\ldots,q_r\) satisfy
\[
(1-\varepsilon)P(X)\le\sum_{j=1}^{r} q_j(X)^2\le(1+\varepsilon)P(X)
\quad\text{for every real }n\times n\text{ matrix }X.
\]
Then
\[
\left\lfloor(n+1)^2/4\right\rfloor\ \le L_\varepsilon(n)\ \le\
\min\{n!,\,O(\varepsilon^{-2}n^2\log(n+1))\}.
\]
In particular fixed relative error gives a polynomial length where exact identities require exponentially many squares by [PR #106](https://github.com/derekblair/math-proofs/pull/106). The upper bound is uniform over all signed real inputs, including those on which the permanent vanishes. It counts square terms. Its individual polynomials can have \(n!\) matching terms each.

The normalized matching image has Gaussian width \(\Theta(n\sqrt{\log n})\) as \(n\to\infty\). In the independent Gaussian row model, a fixed success probability for the uniform relative-error guarantee requires \(\Omega(\varepsilon^{-2}n^2\log n)\) rows, uniformly over \(0<\varepsilon<1\). This does not strengthen the deterministic lower bound.

## Quadratic lower bound

Use the Hall slice from [PR #103](https://github.com/derekblair/math-proofs/pull/103). In an \(a\) by \(n-a+1\) upper-right rectangle use independent real inputs \(y_{ij}\). Set the lower-left block to zero and the upper-left and lower-right to one. Every supported matching uses exactly one of the \(d=a(n-a+1)\) variable edges. Each such edge belongs to \((a-1)!(n-a)!\) supported matchings. Therefore the restriction is \(C\sum_{i=1}^d y_i^2\) with \(C>0\). Every restricted \(q_j\) vanishes at \(y=0\), as the sum of its squares does. Substitute \(ty\), divide by \(t^2\), and take \(t\) to zero. The degree-one parts of the restrictions then give a positive definite quadratic form bounded below by \((1-\varepsilon)C\|y\|^2\). Their common kernel is zero, so there are at least \(d\) squares, maximized by balanced side lengths. This argument allows arbitrary polynomials in the representation.


In fact the uniform upper inequality alone implies matching-monomial support. If an exponent in some summand lay outside the Birkhoff polytope, choose a separating linear weight, perturbed so the finitely many exponents in that summand have distinct weights. On inputs \(x_{ij}=t^{h_{ij}}\), its positive squared leading coefficient would grow faster than \(P\) as \(t\to\infty\). The upper inequality forbids this. The only lattice points of the Birkhoff polytope are permutation matrices, so every admissible representation is a linear sketch of the matching monomial vector. This does not force it to use independent random rows.

## The upper bound and Gaussian width

Write \(F(X)_\sigma=\prod_i x_{i,\sigma(i)}\) and \(T=\{F(X)/\|F(X)\|:F(X)\ne0\}\), where \(X\) ranges over all real matrices. The stated sketch dimension already follows from [Zhang and Kileel, Theorem 2.7 and Example 2.9](https://arxiv.org/html/2506.05174v1): the matching map is a degree-\(n\) polynomial image in \(n^2\) parameters. The following argument independently gives the same upper bound, and also bounds the Gaussian width used below.

For a finite \(\eta\)-separated set of \(L\) points of \(T\) with \(0<\eta\le1\), take \(s=\max(n^2,\lceil\pi\eta^{-1}(2\log L+1)\rceil)\) independent Gaussian hyperplanes through the origin. Each hyperplane separates two unit vectors with probability equal to their angle divided by \(\pi\), at least \(\eta/\pi\). A union bound gives hyperplanes that distinguish all pairs; all signs are strict on this finite set with probability one. Pulling these hyperplanes back through \(F\) gives \(s\) degree-\(n\) polynomials in \(p=n^2\) variables. [Warren's theorem](https://doi.org/10.1090/S0002-9947-1968-0226281-1) bounds their strict sign patterns by \((Cns/p)^p\). Thus for \(u=\log L/p\), one has \(e^u\le C'(n/\eta)(1+u)\le 2C'(n/\eta)e^{u/2}\). This gives \(\log L=O(n^2\log(Cn/\eta))\). A maximal packing also covers \(T\); the entropy integral gives \(w(T)=O(n\sqrt{\log(n+1)})\), with \(w(T)=\mathbb E\sup_{t\in T}|\langle g,t\rangle|\) for a standard Gaussian \(g\). The set is symmetric, since negating one row of \(X\) negates its matching vector.

With \(r\) independent sign rows scaled by \(1/\sqrt r\), the [Liaw–Mehrabian–Plan–Vershynin matrix-deviation inequality](https://arxiv.org/abs/1603.00897) controls the expected uniform norm error by \(O(w(T)/\sqrt r)\). Markov's inequality gives a realization with norm error at most \(\varepsilon/3\) for \(r=O(\varepsilon^{-2}n^2\log(n+1))\). Squaring then gives relative error at most \(\varepsilon\) for \(0<\varepsilon<1\). The sketch coordinates of \(F(X)\) are the polynomials \(q_j\), and zero matching vectors are mapped exactly to zero.

## The matching width lower bound

Use positive inputs \(x_{ij}=e^{\theta_{ij}}\) for \(|\theta_{ij}|\le 1\). Let \(A(\theta)=\log\sum_\sigma\exp(\sum_i\theta_{i,\sigma(i)})\). The Hessian in a direction \(H\) is the variance of \(\sum_i H_{i,\sigma(i)}\) under the corresponding weighted permutation law. Uniformly when \(|\theta_{ij}|\le2\) and \(H\) has zero row and column sums, this variance is at least \(c\|H\|_F^2/n\) for an absolute \(c>0\).

To prove that claim, pair the rows uniformly at random, leaving one uniformly chosen unmatched row if necessary. For a fixed pairing, reveal the unordered pair of assigned columns for each row pair (and any leftover column). The orientations are conditionally independent, each with both probabilities bounded below by an absolute constant, because it changes only two bounded log weights. The conditional variance is therefore at least a constant times the sum of the squared rectangular differences for the revealed pairs. For fixed rows, any ordered assignment of two distinct columns has probability at least \(c'/[n(n-1)]\): relabeling at most four columns maps any given ordered assignment to any other while changing at most four chosen log weights. An unordered row pair occurs with probability at least \(1/n\). Finally,
\[
\sum_{i<j,\,a<b}(H_{ia}+H_{jb}-H_{ib}-H_{ja})^2=n^2\|H\|_F^2,
\]
by expanding and using the zero row and column sums. Taking expectations in the conditional variance bound proves the Hessian claim.

The inner product of normalized matching vectors at parameters \(\theta,\phi\) is \(\exp(A(\theta+\phi)-(A(2\theta)+A(2\phi))/2)\). Thus it is at most \(\exp(-c''\|\theta-\phi\|_F^2/n)\) when their difference is doubly centered. Take the cube generated by the signed patterns \((+,-;-,+)\) on \(\lfloor n/2\rfloor^2\) disjoint \(2\times2\) blocks, with amplitudes in \([-1,1]\). Its maximal \(C_0\sqrt n\)-separated set covers the cube with balls of that radius. In its \(d=\lfloor n/2\rfloor^2\) dimensional subspace each ball has volume at most \((C_1\sqrt{n/d})^d\), whereas the cube has volume of constant side length to the power \(d\). The separated set therefore has size \(\exp(\Omega(n^2\log n))\). For sufficiently large fixed \(C_0\) the normalized matching vectors have pairwise inner products at most \(1/2\). Gaussian Sudakov minoration now gives \(w(T)=\Omega(n\sqrt{\log n})\), matching the upper bound.

## Sharp iid Gaussian row count

Suppose a Gaussian sketch with iid \(N(0,1/k)\) entries succeeds at relative squared-norm error \(\varepsilon\in(0,1)\) on all of \(T\) with probability at least a fixed \(p_0>0\). Its first unscaled row must have \(\sup_{u\in T}|\langle g,u\rangle|\le\sqrt{k(1+\varepsilon)}\). Gaussian concentration and the width lower bound already give \(k\ge c_0n^2\log n\) for all sufficiently large \(n\), uniformly in \(\varepsilon\).

For the sharp dependence on \(\varepsilon\), take a subpacking of \(M=\lfloor\exp(c_1 n^2\log n)\rfloor\) points with pairwise \(|\rho_{uv}|=|\langle u,v\rangle|\le1/2\). Take \(c_1\) sufficiently small that \(k\ge C\log M\) for a sufficiently large absolute \(C\). If \(G,G'\) are independent unscaled sketches, define independent Gaussian matrices \(B=(G-G')/\sqrt2\) and \(C'=(G+G')/\sqrt2\). If both sketches succeed then \(|D_u|\le k\varepsilon\) for every packing point, where \(D_u=\langle C'u,Bu\rangle\), because \(\|Gu\|^2-\|G'u\|^2=2D_u\). With probability \(1-o(1)\) over \(C'\), all \(\|C'u\|^2\) lie in \([k/2,2k]\), by chi-squared concentration and a union bound. Conditional on any such \(C'\), the process in \(B\) is centered Gaussian, with squared increment distance
\[
\|(C'u)\otimes u-(C'v)\otimes v\|^2
\ \ge (1-|\rho_{uv}|)(\|C'u\|^2+\|C'v\|^2)\ \ge k/2.
\]
Sudakov minoration yields mean supremum at least \(c\sqrt{k\log M}\). The supremum is \(\sqrt{2k}\)-Lipschitz in \(B\), so Gaussian concentration makes it at least \(c'\sqrt{k\log M}\) with probability \(1-o(1)\), uniformly on this event for \(C'\). If \(k<c''\varepsilon^{-2}n^2\log n\), the both-succeed event then has probability \(o(1)\), contradicting its probability at least \(p_0^2\). Thus iid Gaussian sketches require \(\Omega(\varepsilon^{-2}n^2\log n)\) rows. The implied constants and large-\(n\) cutoff may depend on \(p_0\) but not on \(\varepsilon\).

## Fixed-accuracy iid sign sketches

The same positive packing also gives the \(n^2\log n\) obstruction for iid sign sketches at fixed accuracy. Include the negatives and write \(b=e^{2n}/\sqrt{n!}\) for an upper bound on the absolute value of every coordinate of every packed vector. Compare the expectations of the maximum under a standard Gaussian row and a sign row via the smooth maximum \(\beta^{-1}\log\sum_v e^{\beta\langle x,v\rangle}\). Its third coordinate derivative is bounded by \(8\beta^2 b^3\). By replacing coordinates one at a time and matching their first two moments, the expectation difference is \(O(\beta^2n!b^3)=o(1)\) for \(\beta=K\sqrt{\log(2M)}\). The smooth-max error is at most \(\log(2M)/\beta\), so sufficiently large fixed \(K\) leaves the sign maximum with expectation \(\Omega(\sqrt{\log M})\). The one-sided Efron–Stein variance bound is at most four: for each replaced sign coordinate, bound the positive difference using a maximizer at the original row, then sum its squared coordinates, which sum to one. Chebyshev's inequality concentrates the maximum above a constant times \(n\sqrt{\log n}\) with probability \(1-o(1)\). The same first-row test gives \(k=\Omega(n^2\log n)\). This does not claim the sharp dependence on varying \(\varepsilon\) for iid signs.

## Reproduction and scope

- Run `node permanent-approximate-square-hall-replay.js` for 35 signed Hall slices, 362,878 matching products, and 140 basis switches.
- Run `node permanent-approximate-width-replay.js` for 90 weighted tables, 88,680 permutations, 24,360 pair probabilities, and 12,180 rectangle terms.
- Compile `PermanentUniformApproximation.lean` with `lake env lean -s 65536 /absolute/path/to/PermanentUniformApproximation.lean` under Lean 4.34.1 and Mathlib at `d13f23b723b8a846827a245b89c10fc7d3f11612`. Lean verifies a rectangle identity and two supporting lemmas, not the Hall, Gaussian width, or uniform approximation theorems.

The iid bounds are not deterministic lower bounds; the gap in optimal deterministic length is at most logarithmic at fixed error. This is a result about the number of polynomial squares, not the cost of evaluating them or of computing the permanent. The uniform guarantee is different from pointwise estimator bounds. The upper bound is an application of existing sketching results, not a new generic sketch theorem. No priority claim is made.
