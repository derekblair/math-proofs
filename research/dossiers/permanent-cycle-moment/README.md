# Exponent improvements for two scalar permanent estimators

Let \(A\) be a nonnegative \(n\times n\) matrix with positive permanent. For each positive-weight permutation \(\sigma\), put \(w_\sigma=\prod_i A_{i,\sigma(i)}\) and \(p_\sigma=w_\sigma/\operatorname{per}(A)\). Take \(\sigma,\tau\) independently from \(p\). Let \(C\) be the number of nontrivial cycles in \(\sigma^{-1}\tau\) and \(C_2\) the number of its transpositions. Then
\[
\mathbb E[2^C]\le (1.396)^n,\qquad
\mathbb E[3^C]\le (1.699)^n.
\]
The constants are exact terminating decimals. These improve the respective classical \((\sqrt2)^n\) and \((\sqrt3)^n\) bounds on the normalized second moment of the cube-root and real-sign determinant-square estimators. The sharp universal rates remain unknown here. This is not a new best algorithm for approximating the permanent; the two estimators are specifically the ordinary scalar determinant estimators, not quaternionic or nonabelian variants.

## 1. A sharp transposition-support bound

First let \(n=2k\), with \(P=\operatorname{per}(A)>0\), and write \(\sigma\sim\tau\) if their relative permutation is a union of \(k\) transpositions. Fix a reference \(\sigma\) of positive weight. Relabel columns by \(\sigma\) and divide each row by its positive diagonal entry, obtaining \(B\) with diagonal 1 and \(\operatorname{per}(B)=P/w_\sigma\). For \(i\ne j\), define the symmetric edge weight \(b_{ij}=\sqrt{B_{ij}B_{ji}}\). Let \(h(T)\) denote the sum of products of these weights over undirected perfect matchings of a subset \(T\), with the empty case 1 and the odd case 0.

We claim
\[
\operatorname{per}(B)\ge \sum_{T\subseteq[n]} h(T)^2
\ge \sum_{T\subseteq[n]} h(T)h(T^c)
= 2^k h([n]).
\]
For the first comparison, group ordered pairs of matchings of \(T\) by their union with multiplicity. Their common edges become directed 2-cycles with the same weight \(b_{ij}^2\). Each simple alternating even cycle of length at least four has two assignments of colors to its edges. The sum of its two directed orientation weights is at least twice their geometric mean, which is the product of \(b_{ij}\) over the cycle. Multiply these comparisons over components. Different unions yield disjoint classes of directed cycle covers, and extending by loops on \(T^c\) does not collide for different \(T\), because \(T\) is exactly the nonfixed support. The second comparison comes from \(2ab\le a^2+b^2\) on complementary sets. The final equality counts each perfect matching of all rows once for every subset of its \(k\) edges.

Here \(h([n])=\sum_{\tau\sim\sigma}\sqrt{w_\tau/w_\sigma}\), so for every \(\sigma\) we have \(\sum_{\tau\sim\sigma}\sqrt{p_\sigma p_\tau}\le2^{-k}\), trivially also when \(p_\sigma=0\). Summing the symmetric inequality
\[
p_\sigma p_\tau\le \tfrac12(p_\sigma+p_\tau)\sqrt{p_\sigma p_\tau}
\]
over ordered neighboring pairs gives \(\Pr(\sigma\sim\tau)\le2^{-k}\). Equality holds for the direct sum of \(k\) equal-weight \(2\times2\) complete blocks.

For any \(n\) and a fixed \(2k\)-element row set \(T\), suppose all its rows are internally covered by relative transpositions. Then \(\sigma(T)=\tau(T)\). Conditional on this common image being a given set \(U\), the restrictions to \(T\) are independent with the weighted matching law of \(A[T,U]\): the total weight of each internal bijection factors by the same complementary permanent. The local bound thus gives probability at most \(2^{-k}\) for the event on \(T\). Summing over row sets gives
\[
\mathbb E\binom{C_2}{k}\le\binom{n}{2k}2^{-k},
\]
and for \(\delta=47/500\),
\[
\Pr\!\left(2C_2\ge(1-\delta)n\right)
\le \sum_{j\le \delta n}\binom{n}{j}2^{-(n-j)/2}
\le \theta^n,\qquad
\theta=2^{-1/2}14^\delta(54/49)<1.
\]
Indeed choose \(t=1/14\) and use \(t^j\ge t^{\delta n}\) in the tail sum, then use \(\sqrt2<10/7\). The exact check of \(\theta<1\) is \(14^{94}54^{1000}<2^{500}49^{1000}\).

## 2. Recursing on the cycle of a random row

Choose a uniform independent pivot row. The probability \(p_2\) that its relative cycle has length two is \(\mathbb E[2C_2/n]\le 0.906+\theta^n\). Thus \(p_2\le0.907\) for every \(n\) above an absolute threshold, uniformly in \(A\).

Reveal the pivot and its relative cycle, including its row set \(T\), common column image \(U\), and both internal bijections. Once these are fixed, the outside restrictions are independent weighted matchings on \(A[T^c,U^c]\), by factorization of the two weights. A cycle of length \(\ell\) contributes the multiplicative factor 1 for \(\ell=1\) and \(q\) otherwise to \(q^C\). Suppose inductively the \((n-\ell)\)-dimensional bound is \(K B^{n-\ell}\). Relative to \(K B^n\), the resulting factor is \(q/B^2\) for \(\ell=2\), and at most \(q/B^3\) for every other \(\ell\), including \(\ell=1\) since \(B^2\le q\). For \((q,B)=(2,349/250)\) and \((3,1699/1000)\) the exact inequality
\[
B^3\ge q(0.907 B+0.093)
\]
holds. Therefore the average factor is at most one. Choose one finite \(K\) covering all sizes up to the uniform threshold, using the trivial \(q^{n/2}\) bound. Finally the moment is multiplicative on block diagonal matrices. Apply \(K B^n\) to a block diagonal sum of \(N\) copies of \(A\), take the \(N\)-th root, and let \(N\to\infty\) to eliminate \(K\).

## 3. Estimators, prior work, and verification

For the estimators, apply independent random signs or cube roots of unity to the entrywise square root of \(A\) and take the squared determinant modulus. Orthogonality gives mean \(\operatorname{per}(A)\). In the expansion of the second moment, group four permuted products by the union of two perfect matchings. In the real-sign case a nontrivial alternating cycle has six allowed assignments to the four slots, compared with two assignments in the squared mean, giving \(3^C\). For cube roots, an elementary exponent imbalance on an edge is in \(\{-2,-1,0,1,2\}\), so it must be zero to survive; this leaves four assignments per cycle, giving \(2^C\). A repeated edge contributes weight exactly once to each paired matching product, and cyclic switches contribute no net determinant sign. The identities and old upper bounds are in Karmarkar–Karp–Lipton–Lovász–Luby, [A Monte-Carlo Algorithm for Estimating the Permanent](https://doi.org/10.1137/0222021), sections 4 and 6, with the worst-case gaps and weighted extension discussed in sections 7 and 8. For different estimators using other algebras, see Chien–Rasmussen–Sinclair, [Clifford algebras and approximating the permanent](https://people.eecs.berkeley.edu/~sinclair/clifford.pdf), and Moore–Russell, [Approximating the Permanent via Nonabelian Determinants](https://doi.org/10.1137/100806709). Bucić et al., [Perfect matchings and derangements on graphs](https://arxiv.org/abs/1906.05908), proves a different fixed-reference intersection bound.

The exact BigInt replay enumerates all Boolean supports up to order four and seeded weighted examples up to order six. It verifies the factorial inequalities and exact moment bounds via integer cross-multiplication, using 69,149 inputs (40,938 positive permanent) and 2,026,478 aggregated nonzero permutation pairs. The Lean file proves the symmetric weighted-pair inequality, the complementary-square sum inequality and the exact pivot and tail arithmetic. The hafnian-to-cycle-cover combinatorics, weighted pivot conditioning and full estimator statements are proved in writing here, not formalized by those Lean lemmas.
