# Signed Boolean lower bound for arbitrary continuous phase masks

Fix \(0<\varepsilon<1\). Suppose fixed complex matrices \(S_1,\ldots,S_r\) with unit-modulus entries and real weights \(w_1,\ldots,w_r\) give a simultaneous relative approximation
\[
(1-\varepsilon)\operatorname{per}(X)
\le \sum_{\ell=1}^{r} w_\ell|\det(S_\ell\circ X)|^2
\le (1+\varepsilon)\operatorname{per}(X)
\]
for every \(X\in\{0,1\}^{n\times n}\). Then
\[
r\ge
\left(\frac{1-\varepsilon}{1+\varepsilon}\right)^2
\left(\frac{7}{6}\right)^{\lfloor n/8\rfloor}.
\]
There is no bound on the size or total absolute value of the signed weights. This proves an exponential lower bound in the unrestricted-weight continuous-phase model omitted by [PR #114](https://github.com/derekblair/math-proofs/pull/114), with a smaller exponent than its bounded-total-variation corollary. The result assumes unit modulus and is a lower bound on the number of fixed masks.

## Boolean table with a rank-three atom

Fix a block size \(m\ge2\). For each pair \(u,v\in\{1,\ldots,m\}\), define a Boolean \(m\times m\) matrix \(X(u,v)\). Its first two rows each have ones precisely in the columns \(\{u,v\}\). If \(u\ne v\), each of the other \(m-2\) rows has one entry, assigning those rows to the complementary columns in increasing order. If \(u=v\), choose any assignment for these rows. The first two rows then share a singleton and no perfect matching is possible.

The local permanent is two if \(u\ne v\) and zero if \(u=v\). For a fixed unit phase mask \(S\) on the block, the filler rows contribute a common factor of unit modulus in the determinant. Set \(z_a=S_{1a}\overline{S_{2a}}\) for every column. Hence the whole table of masked determinant absolute squares, divided by two, is
\[
K_S(u,v)=1-\operatorname{Re}(z_u\overline{z_v}),
\]
including its zero diagonal. Indeed, for distinct columns the two main-row products differ, after division by the unit factor \(S_{2u}S_{2v}\), by \(z_u-z_v\). In matrix form \(K_S=J-aa^{\mathsf T}-bb^{\mathsf T}\), where \(a,b\) are the real and imaginary parts of \(z\). It follows that \(\operatorname{rank}K_S\le3\).

## Tensor product of test blocks

Take \(k=\lfloor n/m\rfloor\) disjoint blocks. The rows and columns of the evaluation table are indexed by \(k\)-tuples \(\mathbf u,\mathbf v\) in \(\{1,\ldots,m\}^k\). The actual input for a table entry is block diagonal with blocks \(X(u_j,v_j)\), and an identity matrix on leftover rows and columns. Normalize the output by \(2^k\).

The target table is \(T=(J-I)^{\otimes k}\). It is one when the two tuples differ in every coordinate and zero otherwise. The table for one global mask is the Kronecker product of its \(k\) local \(K_S\) tables, so its rank is at most \(3^k\). The leftover identity factors have squared determinant one, and off-block mask cells are multiplied by zero. The weighted output table \(Z\) therefore has rank at most \(r3^k\), for arbitrary signs of the weights. On the support of \(T\) every entry of \(Z\) lies in \([1-\varepsilon,1+\varepsilon]\). Off that support, all the determinant squares are zero.

## Approximate rank from a fixed orthogonal test matrix

Take \(H=2J/m-I\). It is symmetric and \(H^2=I\), since \(J^2=mJ\). Its Kronecker power \(B=H^{\otimes k}\) has operator norm one. On the support of \(T\) every entry of \(B\) is the same positive number \((2/m)^k\). There are \([m(m-1)]^k\) ordered entries in that support. Consequently
\[
\langle B,Z\rangle_{\mathrm F}\ge(1-\varepsilon)[2(m-1)]^k,\qquad
\|Z\|_{\mathrm F}\le(1+\varepsilon)[m(m-1)]^{k/2}.
\]
A singular value decomposition of \(Z\) gives \(|\langle B,Z\rangle_{\mathrm F}|\le\sum_j s_j(Z)\le\sqrt{\operatorname{rank} Z}\,\|Z\|_{\mathrm F}\). This uses only the operator norm bound on \(B\) and Cauchy–Schwarz. Combining the inequalities proves the full finite family
\[
r \ge
\left(\frac{1-\varepsilon}{1+\varepsilon}\right)^2
\left(\frac{4(m-1)}{3m}\right)^k .
\]
Choosing \(m=8\) gives the stated bound. The exponent in natural logarithms is \(\log(7/6)/8\) per row, about \(0.01927\). This is enough for an exponential obstruction for arbitrary continuous phases even when large positive and negative weights cancel.

The prior [Boolean result](https://github.com/derekblair/math-proofs/pull/114) still gives stronger rates for finite phase alphabets or controlled weights. The present proof uses signed-rank subadditivity and entrywise relative approximation on a different Boolean family. Mere positivity of output does not supply the Frobenius upper bound and is not asserted here. The same lower bound holds if each mask has separate nonnegative row and column amplitude factors as well as the unit phases: the factors pull out of the determinant, and their squared product can be absorbed into that mask’s signed coefficient. A zero row or column factor gives a zero term. No claim is made for general nonseparable amplitudes, unrestricted permanent algorithms, or historical priority. For the broader approximate-rank framework see Alon–Lee–Shraibman–Vempala, [The Approximate Rank of a Matrix and its Algorithmic Applications](https://eccc.weizmann.ac.il/report/2012/169/). The same-to-all-inputs mask representation differs from the pointwise randomized estimator of [Karmarkar et al.](https://doi.org/10.1137/0222021).

## Exact finite replay

The replay verifies 32,450 local masked determinant and permanent tables using exact fourth-root Gaussian integers, 649 entries of the scaled reflection identity and 2,039,762 tensor entries for exact support and pairing. These are finite checks of the construction and scalar factors. The continuous-phase claim and the rank argument are written proofs. To review, independently check the diagonal \(u=v\), all filler factors, exact zeros, tensor rank multiplication, and the support positivity of the dual witness.

The accompanying Lean file checks the scalar unit-phase atom, the finite reflection-square identity in arbitrary dimensions, and the exact block-eight constant. The rank lower bound and the generic complex Boolean gadget are written arguments, not formalized in Lean here.
