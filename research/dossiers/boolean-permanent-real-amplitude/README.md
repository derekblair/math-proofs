# Boolean permanent approximation with arbitrary real mask amplitudes

Fix \(0<\varepsilon<1\). If a single fixed mixture
\[
\sum_{j=1}^{r} w_j|\det(S_j\circ X)|^2
\]
approximates \(\operatorname{per}(X)\) within factors \(1\pm\varepsilon\) for every Boolean \(n\times n\) matrix \(X\), and each \(S_j\) is an arbitrary real matrix, then
\[
r \ge
\left(\frac{1-\varepsilon}{1+\varepsilon}\right)^2
\left(\frac{32}{27}\right)^{\lfloor n/11\rfloor}.
\]
Entries may have arbitrary magnitudes, signs and zeros. The outer real weights may have any signs, magnitudes and total variation. The proof also covers arbitrary complex masks whose two main-row column vectors, separately in each test block, are scalar multiples of real vectors after a fixed invertible complex \(2\times2\) change of basis. The filler rows of such masks may have arbitrary complex entries. This is a genuine nonseparable-amplitude extension of the rank method in [PR #116](https://github.com/derekblair/math-proofs/pull/116).

## Force a separable filler factor

A local Boolean input \(X(u,v)\) has order \(m+2\), where \(u,v\in\{1,\ldots,m\}\). There are \(m\) private columns and two extra columns \(A,B\). The main two rows have ones precisely in private columns \(u,v\), with a single one per row when the choices agree. Each private column \(i\) has a corresponding filler row \(i\). When \(u\ne v\), filler row \(u\) uses only \(A\), filler row \(v\) uses only \(B\), and all other filler rows use only their corresponding private column. If \(u=v\), the two main rows already preclude a perfect matching. The same filler rule gives the common filler row two allowed extras in this case, with no effect on the zero.

For \(u\ne v\), the permanent is two and the masked squared determinant is the two-by-two squared determinant times a forced filler factor
\[
F(u,v)=A_u B_v\prod_{i\notin\{u,v\}}D_i,
\quad
A_i=|S_{i,A}|^2,\quad B_i=|S_{i,B}|^2,\quad D_i=|S_{i,i}|^2,
\]
where the subscripts in \(S\) refer to filler rows. The magnitude of the sign from placing those forced rows is one. If every \(D_i\ne0\), this factor is separable as \((\prod_i D_i)(A_u/D_u)(B_v/D_v)\). It thus only diagonally scales the main evaluation table. The main determinant square is zero on the diagonal, so this representation extends there independent of the filler-factor convention.

Zero \(D_i\) values also preserve the rank bound. With one zero at an index \(i\), all possible nonzero entries are in row \(i\) or column \(i\) of the evaluation table, giving rank at most two. With two zero indices, only the two ordered pairs of those indices can be nonzero, giving rank at most two. With three or more zeros every entry vanishes. This avoids taking a limit or dividing by a zero mask entry.

## Local rank and tensor lower bound

For real main-row entries \(a_u,b_u\), the table \(M(u,v)=(a_u b_v-a_v b_u)^2\) has rank at most three. Expand it as
\[
(a^{\circ2})(b^{\circ2})^{\mathsf T}+
(b^{\circ2})(a^{\circ2})^{\mathsf T}
-2(a\circ b)(a\circ b)^{\mathsf T}.
\]
The formula provides the rank limit with no assumption on amplitude signs. In the stated complex extension, the change of basis multiplies every minor by one common nonzero number. Scaling each column multiplies its \(u,v\) entry by the product of the squared scalar magnitudes in columns \(u\) and \(v\), preserving the rank bound. Equivalently, the nonzero projective ratios lie in a generalized circle on the Riemann sphere. The proof only needs the stated change-of-basis condition.

Take \(k=\lfloor n/(m+2)\rfloor\) independent blocks and pad by an identity. Divide the evaluation table by \(2^k\). The target is \(T=(J-I)^{\otimes k}\); every mask table has rank at most \(3^k\) by the local result and tensor-product rank. The identity padding contributes a constant to a mask's table. Cross-block mask entries are multiplied by zero. A mixture therefore has rank at most \(r3^k\), independently of the weights.

As in #116, test the approximate table \(Z\) against \((2J/m-I)^{\otimes k}\), an orthogonal matrix that equals \((2/m)^k\) throughout the support of \(T\). Because \(Z\) is zero off that support, its pairing is at least \((1-\varepsilon)[2(m-1)]^k\), whereas its Frobenius norm is at most \((1+\varepsilon)[m(m-1)]^{k/2}\). The pairing is at most \(\sqrt{\operatorname{rank}Z}\|Z\|_{\rm F}\) by singular values. Dividing the resulting rank bound by \(3^k\) gives
\[
r\ge\left(\frac{1-\varepsilon}{1+\varepsilon}\right)^2
\left(\frac{4(m-1)}{3m}\right)^k.
\]
Choose \(m=9\), so there are 11 rows and columns per block and the factor is \(32/27\).

For genuinely arbitrary complex matrices the same gadget gives local rank at most four. The four points \(0,1,i,2\) in the main projective ratio chart realize rank four even before applying filler factors. Thus the rank-three calculation is substantive. One consequence that does survive for arbitrary complex amplitudes is high-accuracy sensitivity: for any \(m\ge5\), choose \(k\le\lfloor n/(m+2)\rfloor\) with \(\varepsilon(m-1)^k<1\). The spectral norm of \(Z-T\) is at most \(\sqrt{\|Z-T\|_1\|Z-T\|_\infty}\). Each of these maximum absolute column and row sums is at most \(\varepsilon(m-1)^k\). The least singular value of \(T\) is one, so \(Z\) has full rank \(m^k\), giving \(r\ge(m/4)^k\) in that accuracy regime. This does not resolve fixed-accuracy arbitrary complex amplitudes.

## Why the same rank witness does not resolve arbitrary complex masks

There is an upper bound of \(O(4^k\varepsilon^{-2}k\log m)\) on the rank needed to approximate this very test tensor with relative error \(\varepsilon\). Independently hash the \(m\) symbols in each coordinate to independent fair bits. One resulting table marks pairs whose bits disagree in every coordinate. It has rank at most \(2^k\), and is identically zero off the support of \(T\). For a pair on the support its indicator is Bernoulli with parameter \(2^{-k}\). Average \(O(2^k\varepsilon^{-2}k\log m)\) independent such tables and scale by \(2^k\). Chernoff's bound and a union bound over at most \(m^{2k}\) pairs give a simultaneous relative approximation. Its rank is at most the sum of the sample ranks. Therefore a rank-only witness on this tensor cannot beat a per-atom rank of \(4^k\) by an exponential factor at fixed \(m\) and \(\varepsilon\). Other input families or additional structure remain possible.

## Verification

Exact Gaussian-integer replay verified 38,940 local Boolean evaluations over 660 fixtures, including zero through three diagonal fillers and an invertible complex change of basis applied to real main vectors. It computed all local table ranks by exact integer elimination, including 142 at rank three and the unrestricted complex rank-four witness. The full theorem is a written argument. No priority or algorithmic claim.

The Lean file proves the real rank-three atom expansion as an algebraic identity, the exact finite forced-product/separation identities, and the block-nine arithmetic. It does not formalize the tensor rank lower bound. For background on approximate rank see [Alon–Lee–Shraibman–Vempala](https://eccc.weizmann.ac.il/report/2012/169/). This restricted uniform mask representation also differs from [Landsberg–Ressayre’s determinantal-complexity result with symmetry](https://arxiv.org/abs/1508.05788) and from the pointwise estimator of [Karmarkar et al.](https://doi.org/10.1137/0222021).
