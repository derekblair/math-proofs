# Exact permanents with hierarchical sibling low rank

**Theorem (written proof).** Let an exact rational square matrix of order $n$ be specified by a paired binary partition of its rows and columns, square leaf blocks of order at most $s$, and two directed rank factorizations for the off-diagonal sibling blocks at each internal node. Write $m_v$ for the order of node $v$, and $r_v$ for the sum of the two factor ranks after redundant columns are removed. Then its permanent can be computed deterministically in polynomial workspace and time
$$\operatorname{poly}(L)\,2^{O(s+\max_P\sum_{v\in P}r_v\log(1+m_v/r_v))}.$$
where $L$ is input bit length, $P$ ranges over root-to-leaf paths, and a zero rank contributes zero. If every child has order at most a fixed fraction of its parent's order and every $r_v\le r\le n$, the exponent is $O(s+r\log^2(1+n/r))$ for $r>0$; for $r=0$ it is $O(s)$. The same bounds hold over a finite field given by its prime and defining irreducible polynomial, with supplied exact factorizations. In particular the balanced uniform bound is subexponential if $s=o(n)$ and $r=o(n)$.

The input promise is on the supplied hierarchy, not the rank or sparsity of the entire matrix. Nothing here improves the bound for arbitrary dense input.

## 1. Partial matchings and the local contraction

For a node $W$, let $Z_W(a,b)$ sum the weights of all its partial bipartite matchings. Each matched edge contributes its matrix entry; unused row $i$ and column $j$ respectively contribute monomer weights $a_i,b_j$. Zero monomers at the root give the permanent. At a leaf, enumerate equal-cardinality matched row and column subsets and compute the permanent of each induced square submatrix by Ryser's formula, with polynomial space and $2^{O(s)}$ arithmetic operations.

At an internal node give each rank-one summand of either directed sibling block a separate color $j$. Let $X_j$ and $Y_j$ mark row and column endpoints of that color. To evaluate a polynomial $F(X,Y)$, add the appropriate sums of $U_{ij}X_j$ and $V_{ij}Y_j$ to the monomer weights of each child and multiply its two partial-matching evaluations. These additions affect only the endpoints incident to that directed block. If the node has order $m$, the total degree of $F$ is at most $2m$.

Expand each monomer sum. Every unused vertex in a child is then either unused at the parent or marked with exactly one crossing color. For a multiplicity vector $\alpha$, only the monomial $X^\alpha Y^\alpha$ contributes: its marked row and column sets pair in $\prod_j\alpha_j!$ ways, each yielding the same product of factors. The exact node contraction is therefore
$$
Z_W(a,b)=\sum_{|\alpha|\le m}\Bigl(\prod_j\alpha_j!\Bigr)[X^\alpha Y^\alpha]F(X,Y).
$$
This counts all terms of the expansion of the matrix entries, including when several rank-one colors are nonzero on the same edge. Signed weights need no positivity assumption.

## 2. Newton simplex evaluation

Let $D=2m$, $r=r_v$, and $Z=(X,Y)$. Multivariate Newton interpolation expands $F$ as
$$
F(Z)=\sum_{|\beta|\le D}(\Delta^\beta F)(0)\prod_{q=1}^{2r}\binom{Z_q}{\beta_q}.
$$
Indeed, the products of falling-factorial binomials of total degree at most $D$ form a triangular basis, and applying a coordinate difference lowers its binomial index by one. The difference of order $\beta$ at zero consequently picks out exactly that basis coefficient.

For one color, the contraction of a basis factor is
$$
\ell(a,b)=\sum_k k!\,[T^k]\binom{T}{a}\,[T^k]\binom{T}{b}.
$$
The full contraction is the product of these values, since the degree budget already bounds the matched multiplicity. Expanding the finite differences gives the weight of the point $\gamma$ as
$$
\sum_{\beta\ge\gamma,\ |\beta|\le D}(-1)^{|\beta-\gamma|}\binom{\beta}{\gamma}\prod_{j=1}^r\ell(\beta_j,\beta_{j+r}).
$$
Here the vector binomial is a product of coordinate binomials. Compute a weight without enumerating $\beta$: for each color and all $a\ge\gamma_j$, $b\ge\gamma_{j+r}$ with $a+b\le D$, put its signed binomial-weighted $\ell(a,b)$ into a univariate array at index $a+b$. Multiply the $r$ arrays truncated at degree $D$ and sum the surviving entries. All of this takes polynomial work and space per point; one may scale each color by $(D!)^2$ and divide at the end by $(D!)^{2r}$.

Enumerate simplex points on demand. There are exactly $\binom{2m+2r}{2r}$ candidate evaluations, each requiring at most one call to each child. A rank-zero node asks each child only once and multiplies the two results.

An alternate evaluator first selects homogeneous degree $2|\alpha|$ by univariate interpolation on $F(tX,tY)$, then applies the mixed forward differences of order $(\alpha,\alpha)$ at zero. The target monomial receives the multiplier $(\prod_j\alpha_j!)^2$ and every other monomial of that degree is annihilated in at least one coordinate. Dividing by one factorial product gives the desired contracted term. This is the evaluator checked by the small recursive replay and the source of the separate Lean ingredient.

## 3. Bit complexity and recursion

Over the rationals, take a common denominator $Q$ of all entries of the leaf blocks and of all entries of the supplied factors. Multiply leaves by $Q^2$ and each factor by $Q$, and divide the final permanent by $Q^{2n}$. Integer monomers remain integer during evaluation. Each child's true output at such weights is integral, so the exact divisions after the signed scaled sums have no remainder. A node value before division is a sum of integer products with polynomial bit length: semantic child values sum at most exponentially many terms in a polynomial in the input length, each product uses at most $2m$ endpoint or edge weights, and the scaled binomial and factorial factors add polynomially many bits. Monomer augmentation adds only polynomial-bit factors times bounded grid coordinates along a path. The number of summed terms has polynomial logarithm. The recursion stores polynomial work and accumulators per frame and evaluates the children sequentially. It does not memoize exponential tables.

For finite fields, first compress factors over the field, then lift the leaf and factor entries to their degree-less-than-$e$ representatives in $\mathbb Z[T]$, where the field is $\mathbb F_p[T]/(f)$ and $e=\deg(f)$. Run the same algorithm with integer polynomials (exact scalar divisions coefficientwise), and reduce the final polynomial modulo $(p,f)$. The lifted factors define the integer-polynomial matrix; no equality with independent lifts of dense entries is needed. Products have degree $O(ne)$, and their coefficients have polynomial bit length by the same bounds, with a polynomial logarithmic contribution from coefficient convolution. In particular the algorithm never divides by a factorial in the field.

Each directed block rank may be capped by its smaller dimension via exact linear algebra, so $r_v\le m_v$. For positive $r_v$ the logarithm of the local evaluation count is $O(r_v\log(1+m_v/r_v))$. The number of invocations of any node is bounded by the product of evaluation counts at its ancestors. Sum the work per invocation over the $O(n)$ nodes, with polynomial bit cost at internal nodes and a $2^{O(s)}$ factor at leaves. Rank-zero nodes contribute no multiplicative overhead to the path bound. For balanced splits, the levels with $m_v\ge r$ have $O(\log(1+n/r))$ terms, each at most $O(r\log(1+n/r))$; the remaining sizes form a geometric tail, and each contribution is $O(m_v)$. This yields the uniform bound without an additive $\log^2 n$ term.

## Reproduction and scope

- `node hierarchical-audit.js` compares 40 exact signed-integer partial/perfect matching evaluations (38 nonzero) on small depth-two trees to direct enumeration. Test memoization is only a speed aid for the replay, not part of the polynomial-space algorithm.
- `node newton-simplex-audit.js` compares the simplex contraction and exact point count against 105 signed polynomial inputs. It materializes small simplex test sets; the algorithm in the proof enumerates them on demand.
- Run `lake env lean -s 65536 /absolute/path/to/ForwardGrid.lean` from a Lean 4.34.1 project with Mathlib at commit `d13f23b723b8a846827a245b89c10fc7d3f11612`. The three audited Lean statements check the explicit grid formula, same-degree monomial isolation, and finite homogeneous sums over a commutative ring. They do not formalize the recursive matching algorithm, the Newton evaluator, or either complexity bound.

## Context

[Barvinok, §3.3](https://www.math.ucdavis.edu/~deloera/MISC/LA-BIBLIO/trunk/Barvinok/tspalgorithmicold.pdf) already uses factorial contraction for global low rank. [Hatami's exposition of the sparse-permanent argument, Proposition 2.1](https://www.cs.mcgill.ca/~hatami/expositions/ETH.pdf), attributed to O'Donnell and Hatami, is a flat block-plus-low-rank baseline used for sparse interpolation. [Flarup and Lyaudet](https://arxiv.org/abs/0801.3408) use bounded weighted clique-width, a different promise involving labels with uniform inter-label weights. The representation itself is established in numerical matrix algorithms, for example [Aminfar, Ambikasaran, and Darve](https://arxiv.org/abs/1403.5337). No priority claim is made.

### Full external cuts and Anwar's algorithm

[Anwar, Theorems 3.1–3.2](https://arxiv.org/html/2611.17812v1#S3), gives exact permanent algorithms parameterized by the sum of the ranks of the two directed **full external cuts** at each node. The algorithm propagates arrays of partial-matching coefficients in endpoint coordinates. Fixed cut width gives polynomial time, with polynomial bit complexity for rational inputs. In characteristic $p$, it uses at most $p^k$ coefficients per node of width at most $k$ and $p^{O(k)}\operatorname{poly}(n)$ field operations and zero tests overall; in particular, fixed $p$ and $k=O(\log n)$ give polynomial time.

The two promises overlap. In the supplied sibling tree, the exterior of a node is partitioned by its ancestor sibling sets. Each directed cut block against such a set is a restriction of the corresponding ancestor's sibling block. Subadditivity of rank under concatenation therefore bounds the node's full cut width by the sum of sibling-rank sums along its ancestor path. Refining a leaf of order at most $s$ to singleton leaves contributes at most $2s$ to that bound from within the original leaf. Thus the balanced tree with fixed $r$ and $s$ has full cut width $O(\log n)$, and Anwar's algorithm already gives polynomial time in fixed characteristic, which can be faster than the bound in this dossier. Anwar's stated array-based algorithm does not provide the polynomial-workspace guarantee of this dossier for general growing widths. Our time bound is instead expressed in the local sibling ranks along the given hierarchy. No historical priority is asserted.
