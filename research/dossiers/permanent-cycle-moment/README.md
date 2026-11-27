# Exponent improvements for two scalar permanent estimators

Let \(A\) be a nonnegative \(n\times n\) matrix with positive permanent. For each positive-weight permutation \(\sigma\), put \(w_\sigma=\prod_i A_{i,\sigma(i)}\) and \(p_\sigma=w_\sigma/\operatorname{per}(A)\). Take \(\sigma,\tau\) independently from \(p\). Let \(C\) be the number of nontrivial cycles in \(\sigma^{-1}\tau\) and \(C_2\) the number of its transpositions. Then
\[
\mathbb E[2^C]\le (1.3112)^n,\qquad
\mathbb E[3^C]\le (1.5451)^n.
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

## 2. A sharp bound at any fixed pivot row

Fix a row \(v\), and write \(P_\ell\) for the probability that the relative cycle through \(v\) has length \(\ell\). Partition the ordered pairs \((\sigma,\tau)\) by their nontrivial relative cycles **not** containing \(v\), recording both full restricted bijections on the union of those frozen cycles. Each part leaves the same residual row set and the same residual column set for both matchings. The frozen product of weights is a constant. Within the residual submatrix, each pair has at most one nontrivial relative cycle, and that cycle must contain \(v\). Conversely every residual pair with that property belongs to the part.

On the positive-weight residual permutations, draw an edge when the two permutations differ by one transposition through \(v\) (a star transposition). The graph is triangle-free by permutation parity. Distinct vertices at graph distance two differ by a product of two different star transpositions, and hence by a three-cycle through \(v\). Distances are in this induced graph; not every three-cycle need arise.

Here is the needed form of the classical [Hoffman–Pereira copositivity criterion](https://research.ibm.com/publications/on-copositive-matrices-with-1-0-1-entries). For any finite triangle-free graph and nonnegative vertex weights \(x_i\), let \(D=\sum_i x_i^2\), let \(E\) be the sum of \(x_i x_j\) over ordered adjacent pairs, and let \(D_2\) be the corresponding sum over ordered distance-two pairs. Then \(E\le D+D_2\). To see this, consider \(D+D_2-E\). If two distance-two vertices have positive weights, keep their total weight fixed and vary its allocation. Their two diagonal terms and mutual term together give the square of the total; all other couplings depend affinely on the allocation. Moving the entire mass to one end therefore does not increase the quadratic form and removes a positive coordinate. Repeat. On the final support the edge graph has maximum degree one, since two positive neighbors of any positive vertex would be at distance two. The form is now a sum of squares from isolated vertices and squared differences from edges.

Apply the inequality to \(x_i\) equal to the residual matching weights. Diagonal pairs have pivot cycle length one; adjacent pairs are exactly the pivot transpositions; distance-two pairs have pivot cycle length three. Multiply by the frozen weights, sum over parts, and normalize by the square of the permanent. This gives
\[
P_2\le P_1+P_3 \quad\text{and in particular}\quad P_2\le\tfrac12.
\]
The one-half bound is attained by any matrix with an isolated, uniformly weighted complete \(2\times2\) block containing the pivot.

## 3. Randomly thin the quadratic form

Within each residual part of dimension \(m\), give the pivot row label 0. Independently give every other row and column label 0 with probability \(s\) and label 1 otherwise. Retain a residual permutation only when the labels agree along every matching edge, setting its weight to zero otherwise. Write \(H=s^2+(1-s)^2\). A single permutation survives with probability \(sH^{m-1}\).

If two permutations differ only on a relative cycle of length \(\ell\) through the pivot, their combined support consists of \(m-\ell\) isolated edges and one alternating cycle on \(2\ell\) vertices. The alternating cycle must have label 0 on all vertices, because it contains the pivot. Thus the joint survival probability is \(s^{2\ell-1}H^{m-\ell}=sH^{m-1}p^{\ell-1}\), with \(p=s^2/H\). Every \(p\in(0,1)\) is possible, by choosing \(s/(1-s)=\sqrt{p/(1-p)}\). Apply copositivity to the original graph with the thinned vertex weights; it is important not to recompute the distance-two relation after thinning. Taking expectations and dividing out the common positive factors gives \(E\le p^{-1}D+pD_2\). Multiply by the frozen weights and sum the parts as before:
\[
P_2\le p^{-1}P_1+pP_3,\qquad 0<p<1.
\]

## 4. Cycle recurrence and the new exponents

Reveal the actual pivot cycle, recording its row set \(T\), its common column image \(U\), and both internal bijections. Conditional on that record, the outside restrictions are independent weighted matchings on \(A[T^c,U^c]\), because their weights factor. Inductively bounding the outside moment by \(B^{n-\ell}\), the contribution divided by \(B^n\) is at most \(B^{-1}\) at \(\ell=1\), and \(q B^{-\ell}\) at \(\ell\ge 2\). Set
\[
a=1-B^{-1},\quad d=q B^{-2}-1,\quad c=1-q B^{-3}.
\]
For \(B\ge1\) and \(a,c,d\ge0\), the conditional upper bound above averages to at most \(1+dP_2-aP_1-cP_3\); longer cycles only improve it. It is at most one whenever
\[
d/p\le a,\qquad dp\le c.
\]
For \(q=2\) use \(B=13112/10000\), \(p=6889/10000\). For \(q=3\) use \(B=15451/10000\), \(p=14549/20000\). The inequalities are checked by exact rational arithmetic. The base case \(n=0\) has moment one; the induction proves the advertised bounds without a multiplicative prefactor.

The condition \(d^2\le ac\) is the limit of this pointwise certificate, not of the true moment. To see the distinction, take diagonal entries 1 and add only bidirectional star edges through \(v\), giving each transposition matching weight \(y/(m-1)\) and the identity weight 1. For the pivot, the unnormalized masses of lengths one, two and three tend respectively to \(1,2y,y^2\) as \(m\to\infty\). Thus asking \(dP_2\le aP_1+cP_3\) for every weighted input necessarily requires \(a-2dy+cy^2\ge0\) for every \(y\ge0\), hence \(d^2\le ac\) when \(a,c,d>0\). The recursive minors in this example are much easier than the worst-case bound, so this argument does not lower-bound the true optimal exponent.

## 5. Estimators, prior work, and verification

For the estimators, apply independent random signs or cube roots of unity to the entrywise square root of \(A\) and take the squared determinant modulus. Orthogonality gives mean \(\operatorname{per}(A)\). In the expansion of the second moment, group four permuted products by the union of two perfect matchings. In the real-sign case a nontrivial alternating cycle has six allowed assignments to the four slots, compared with two assignments in the squared mean, giving \(3^C\). For cube roots, an elementary exponent imbalance on an edge is in \(\{-2,-1,0,1,2\}\), so it must be zero to survive; this leaves four assignments per cycle, giving \(2^C\). A repeated edge contributes weight exactly once to each paired matching product, and cyclic switches contribute no net determinant sign. The identities and old upper bounds are in Karmarkar–Karp–Lipton–Lovász–Luby, [A Monte-Carlo Algorithm for Estimating the Permanent](https://doi.org/10.1137/0222021), sections 4 and 6, with the worst-case gaps and weighted extension discussed in sections 7 and 8. For different estimators using other algebras, see Chien–Rasmussen–Sinclair, [Clifford algebras and approximating the permanent](https://people.eecs.berkeley.edu/~sinclair/clifford.pdf), and Moore–Russell, [Approximating the Permanent via Nonabelian Determinants](https://doi.org/10.1137/100806709). Huber, [Exact Sampling from Perfect Matchings of Dense Regular Bipartite Graphs](https://doi.org/10.1007/s00453-005-1175-9), uses a pivot cycle in the all-ones case. The use of a frozen outside-cycle record and a thinned star-transposition inequality controls arbitrary weights here. Bucić et al., [Perfect matchings and derangements on graphs](https://arxiv.org/abs/1906.05908), proves a different fixed-reference intersection bound.

For a relative-error estimate with failure probability at most \(\eta\), independent averaging and median amplification require \(O(B^n\varepsilon^{-2}\log(1/\eta))\) estimator evaluations by the second-moment bound. On Boolean supports it also follows from Cauchy–Schwarz that a real random sign mask is nonsingular with probability at least \((1.5451)^{-n}\) when a perfect matching exists. Hence a union bound gives a nonconstructive family of \(O(n^2(1.5451)^n)\) real sign masks that hits every Boolean support with a perfect matching. This does not match the known block-based lower exponent and is not a deterministic construction.

The exact BigInt replay enumerates all Boolean supports up to order four and seeded weighted examples up to order six. It verifies the factorial inequalities, both fixed-pivot inequalities and both exact moment bounds on 69,149 inputs (40,938 with positive permanent), using 2,026,478 nonzero unordered permutation pairs. It also enumerates biased row/column labels for 89 relative permutations to check the thinning probabilities exactly. The Lean files prove supporting finite algebra and exact constants; the cycle grouping, random thinning and full estimator statements are proved in writing here, not formalized in Lean.
