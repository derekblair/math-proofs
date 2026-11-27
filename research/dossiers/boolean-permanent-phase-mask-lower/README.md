# Boolean permanent approximation with fixed phase-masked determinants

A mixture is \(A(X)=\sum_{j=1}^r w_j|\det(S_j\circ X)|^2\) with fixed unit-modulus complex masks and real signed weights. Assume \(A(X)\) approximates \(\operatorname{per}(X)\) to relative error \(0<\varepsilon<1\) on every Boolean matrix. On this domain \(\operatorname{per}(X^{\circ2})=\operatorname{per}(X)\). Write \(W=\sum_j|w_j|\), \(k=\lfloor n/2\rfloor\), and \(B_k=4^k/\binom{2k}{k}=\Theta(\sqrt{k+1})\).

Two lower bounds hold.

1. If every phase is a \(K\)th root of unity for an integer \(K\ge2\), then
\[
r\ge B_k^{-1}\left(\frac K{K-1}\right)^k.
\]
The result permits arbitrary signed weights and uses only positivity of the output on the test matrices. Real sign masks give the explicit bound \(\binom{2k}{k}/2^k=\Theta(2^k/\sqrt{k+1})\).
2. For arbitrary unit complex phases and every \(0<t<1\),
\[
r^{1-t}W^t\ \ge\ \frac{(1-\varepsilon)^t}{B_k C_t^k},
\qquad
C_t=2^t\frac{\Gamma(t+1/2)}{\sqrt{\pi}\Gamma(t+1)}.
\]
In particular, fixed accuracy and subexponential \(W\) require \(r\ge\exp(((1-\log 2)/2-o(1))n)\). Nonnegative weights automatically have \(W\le1+\varepsilon\) by testing a permutation matrix. The same exponent applies to signed weights with subexponential total variation. No claim is made for that exponent at unrestricted total variation.

These are Boolean test results. [PR #108](https://github.com/derekblair/math-proofs/pull/108) uses signed real input matrices for its stronger exponent \(1\) and assumes nonnegative weights.

## Test matrices and conditional moments

Fix \(k\) disjoint row pairs. Start with a uniformly random permutation of the columns. If \(n\) is odd, first reserve its final column for the single leftover row. Assign the remaining columns in consecutive pairs to the row pairs. The test matrix is all ones on the resulting \(2\times2\) blocks, and has a single one in the leftover row if needed. Its permanent is \(2^k\).

For one mask and one row pair, write the ratios of its two row entries in each still available column as \(\exp(i\theta_a)\). If columns \(a,b\) are chosen for the next block, its determinant absolute square divided by its permanent \(2\) is
\[
Y=1-\cos(\theta_a-\theta_b).
\]
The mask's full ratio \(R=|\det(S\circ X)|^2/\operatorname{per}(X)\) is the product of these local ratios. Conditional on the earlier column assignments, the next pair is a uniform ordered distinct pair in the remaining list, of even size \(m\). Thus any upper bound \(u\) on the corresponding with-replacement probability of \(Y>0\) or the fractional moment of \(Y\) transfers to \(u\,m/(m-1)\) for sampling without replacement. Same-column draws give zero. Successive conditioning multiplies the factors, with \(\prod_{h=1}^k 2h/(2h-1)=B_k\).

For \(K\)th roots let \(p_a\) be the proportions of the \(K\) possible row ratios. The with-replacement chance of nonzero determinant is \(1-\sum_a p_a^2\le1-1/K\). Therefore any mask is nonzero on at most a proportion \(B_k(1-1/K)^k\) of the block matrices. If fewer masks than its reciprocal were used, the union bound would leave a Boolean input with all terms zero, irrespective of their weights. This proves the alphabet result.

For every finite alphabet of \(K\)th roots, iid masks survive with probability \(((K-1)/K)^k\) on each fixed test matrix. A union bound over at most \(n!\) matrices therefore shows the exponent of the support-cover size is sharp on this family for each fixed \(K\). For \(K=2\) and \(K=3\), the approximation exponent is sharp on the block test family itself. Sample iid \(K\)th-root masks. On each fixed test matrix the ratio is \((K/(K-1))^k\) with probability \(((K-1)/K)^k\) and zero otherwise. This follows from the one common nonzero squared chord length for each of these alphabets. Equal weights on \(O(\varepsilon^{-2}(K/(K-1))^k n\log(n+1))\) samples approximate all those test matrices simultaneously by the binomial Chernoff bound and the union bound over at most \(n!\) matrices for fixed row pairs.

## Arbitrary phases and the signed-weight tradeoff

For any probability measure \(\mu\) on the circle and \(0<t<1\), two independent angles from \(\mu\) obey
\[
\mathbb E_{\mu\otimes\mu}(1-\cos(\theta-\phi))^t\le C_t.
\]
One proof starts with the positive Laplace integral \(y^t=c_t\int_0^\infty(1-e^{-sy})s^{-t-1}\,ds\) for \(y\ge0\). For fixed \(s>0\), the absolutely convergent expansion of \(e^{s\cos u}=e^{(s/2)e^{iu}}e^{(s/2)e^{-iu}}\) has nonnegative Fourier coefficients. The expectation of its \(j\)th character on \(\theta-\phi\) is \(|\widehat\mu(j)|^2\). Thus \(\mathbb E e^{-s(1-\cos(\theta-\phi))}\) is at least its value for uniform angles. Integrating in \(s\) proves the bound, and the uniform-angle integral gives the stated beta-function value \(C_t\). This is a direct circle instance of the classical positive definite kernel method. [Schoenberg](https://doi.org/10.1090/S0002-9947-1938-1501980-0)

The conditioning argument now gives \(\mathbb E R^t\le B_k C_t^k\) for each mask. On each test input, \(1-\varepsilon\le\sum_j w_j R_j\le\sum_j|w_j|R_j\). Raise to power \(t\), apply subadditivity of \(x^t\), and average. Concavity across the \(r\) weights gives
\[
(1-\varepsilon)^t\le B_k C_t^k\sum_j|w_j|^t
\le B_k C_t^k r^{1-t}W^t .
\]
To take the asymptotics, \(C_1=1\) and the logarithmic derivative at 1 is \(1-\log 2\), from the gamma expression and the digamma half-integer recurrence. Set \(t=1-\delta_n\) with \(\delta_n\to0\) slowly enough that \(\log(n+1)+\log_+ W=o(n\delta_n)\). This is possible for subexponential \(W\). Taking logs of the finite inequality gives the asserted exponent. The finite inequality also states the exact tradeoff for any \(\varepsilon\) and \(W\).

For continuous phases mere support coverage requires only one generic mask: for each Boolean support possessing a perfect matching, the determinant as a function of the independent phases is a nonzero trigonometric polynomial, since a surviving permutation contributes its own distinct character. Its zero set has Haar measure zero, and there are only finitely many Boolean supports. Support coverage alone does not give relative approximation.

## Verification and adjacent literature

The exact alphabet replay enumerated or sampled 7,465 systems of row ratios, and tested 5,709,124 column arrangements through order eight. It found no violations, including 14 equality cases across the checked bounds. The analytic fractional-moment result is a written argument. The classical block-diagonal \(2\times2\) witness for iid determinant estimators is an antecedent. Here the column pairing is randomized against an arbitrary fixed family, and the conclusion concerns simultaneous Boolean approximation, signed weights, or a total-variation tradeoff. [Karmarkar–Karp–Lipton–Lovász–Luby](https://doi.org/10.1137/0222021)

Run `node boolean-permanent-phase-mask-cover-replay.js` to reproduce the finite check. `BooleanPhaseMaskArithmetic.lean` checks only `alphabet_cauchy`, `pairing_factor_step`, and `finite_cover_budget` under Lean 4.34.1 and mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. Neither the continuous Fourier argument nor the full theorem is formalized. The test-family upper bound does not assert an approximation upper bound on all Boolean inputs. The signed exact order-four result in [PR #104](https://github.com/derekblair/math-proofs/pull/104) concerns a different question. No priority claim is made.
