# A one-cell lattice coloring with an explicit polynomial prefactor

Let \(\beta=3\sqrt{3}/2\) and
\[
c_*=\frac{3\sqrt 2}{4}\max_{\lambda>0}\lambda\int_0^1 e^{-\lambda x^{1/3}}\,dx
=0.54093165\ldots.
\]
There is a Borel unit-distance coloring of \(\mathbb R^d\) with at most
\[
\left(c_*^{-1}+o(1)\right)d\log d\,\beta^d
\]
colors. All classes can be assigned from a cover by translates of one periodic independent set. That set is a union of lattice translates of a single centrally symmetric convex cell. In particular there is one clipped cell per fundamental domain, rather than a random collection of independent centers within a cell of the period lattice.

[Davies, §10](https://arxiv.org/html/2610.12301v1#S10) uses bisector clipping with an iid center sample and period \(2\mathbb Z^d\). [PR #119](https://github.com/derekblair/math-proofs/pull/119) derives the sharp margin-dependent raw-density asymptotic for that model and finds \(c_*\). Here a single random lattice attains the same asymptotic density lower bound. Its covolume is small enough that the torus net has logarithmic size \((1+o(1))d\log d\). Taking the margin \(o(1/d)\) avoids an exponential loss in the density. This is an upper bound with the same exponential base as Davies.

## A clipped lattice cell

Take \(\varepsilon=1/(d\log d)\) for large \(d\), \(R=(1-\varepsilon)/2\), and \(A=1+\varepsilon\). For a lattice \(\Lambda\) define
\[
K=\{ x:\|x\|<R,\quad x\cdot u<(\|z\|-A)/2
\text{ for every }z\in\Lambda\setminus\{0\},\ u=z/\|z\|\}.
\]
Only lattice vectors of length below two affect the open ball. This is an open convex set, centrally symmetric by pairing \(z\) with \(-z\). Two points of \(K\) are at distance less than \(1-\varepsilon\). For \(x,z+y\) from two different translates, the opposite cuts make their difference have projection greater than \(A\) along \(z\). Hence \(K+\Lambda\) avoids the distance band \([1-\varepsilon,1+\varepsilon]\), its cells are disjoint, and its torus density is \(|K|/\operatorname{covol}(\Lambda)\). If \(K\) is nonempty then the shortest nonzero lattice vector is longer than \(A\). Otherwise the opposite inequalities for a shortest vector would have no joint solution.

For an offset \(x\) of length \(r\), its forbidden displacement region \(F_x\) has radial function \(A+2r u\cdot\widehat x\). A boundary of measure zero can be included to encode the strict cut. Let \(v_d\) denote unit-ball volume and
\[
g(r)=\max_{0\le t\le 1}(A+2rt)\sqrt{1-t^2}.
\]
The radial estimate and Laplace calculation from #119, without any torus projection, give
\[
\frac{|F_R|}{v_d g(R)^d}\to\frac{4}{3\sqrt2},\qquad
\frac{|F_{R x^{1/d}}|}{|F_R|}\to x^{1/3}\quad(0<x\le1).
\]
Here \(F_r\) denotes a forbidden region at any offset of length \(r\), since volume is rotationally invariant. For the first relation the angular saddle tends to \(t=1/2\), where the second derivative of the logarithmic angular profile is \(-8/3\). The second relation follows from the boundary envelope derivative \(d\log g/d\log r\to1/3\), uniformly between \(R x^{1/d}\) and \(R\) for fixed \(x>0\), and the same Laplace prefactor. These facts also give \(|F_r|=O(|F_R|)\) uniformly, or use convexity and evenness of the angular integral as a function of signed \(r\).

## A random lattice attains the density lower bound

Write \(V=|F_R|/\lambda\), where \(\lambda>0\) is arbitrary and fixed. Use a Haar-random covolume-one lattice dilated by \(V^{1/d}\). The forbidden set is generally asymmetric. Since a lattice is closed under negation, select a measurable antipodal representative set from \((F_x\cup(-F_x))\setminus\{0\}\), for example the points whose first nonzero coordinate is positive. Its volume is
\[
|F_x|-\tfrac12|F_x\cap(-F_x)|.
\]
The void event for this representative set is exactly the event of retaining \(x\). The intersection is contained in the ball of radius \(A\), because its radial function is \(A-2r|u\cdot\widehat x|\). Thus the difference between its representative volume divided by \(V\) and \(|F_x|/V\) is exponentially small, uniformly in \(x\). Indeed \(v_d A^d/V=O((A/g(R))^d)\), and \(A/g(R)\to 4/(3\sqrt3)<1\).

After scaling by \(V^{-1/d}\) the representative set is antipodal-free and has volume bounded by a constant. The random-lattice void estimate therefore gives
\[
\Pr(x\in K)=\exp(-|F_x|/V)+o(1)
\]
uniformly for \(\|x\|<R\). One may apply [Klartag, Theorem 1.2](https://arxiv.org/html/2605.10479v1#Thmtheorem1.2), which gives exponential total variation error and also credits Schmidt's earlier void estimate. The hypotheses apply to arbitrary measurable antipodal-free sets of volume at most \(c d\), so the shapes here can vary with both \(x\) and \(d\).

Integrate over the ball using volume coordinate \(u=(r/R)^d\). By the preceding limits and dominated convergence, the expected density is
\[
\left(\frac{R}{g(R)}\right)^d
\left[\frac{3\sqrt2}{4}\lambda\int_0^1 e^{-\lambda u^{1/3}}\,du+o(1)\right].
\]
Taking \(\lambda\) at the fixed optimum and choosing a lattice that attains at least this density up to \(o(\beta^{-d})\) gives \(p\ge(c_*-o(1))\beta^{-d}\). To compare the exponential factors, \(g(R)\) is between \(3\sqrt3/4\) and \((1+\varepsilon)3\sqrt3/4\). This follows from the angular formula on \(0\le t\le1\), where \(A+2Rt=1+t+\varepsilon(1-t)\). Since \(d\varepsilon\to0\), \((R/g(R))^d\sim\beta^{-d}\).

An elementary-density fallback uses only the Siegel mean to lower bound the void probability by \((1-|F_x|/V)_+\). The same integration gives density prefactor \(3\sqrt2/4\) times \(\lambda\int_0^1(1-\lambda u^{1/3})_+du\). Its maximum is \(1/3\), attained at \(\lambda=2/3\), yielding \(\sqrt2/4\) in place of \(c_*\) and the same \(d\log d\) order. The full Poisson statement is only needed to obtain the better leading constant.

## Cover the smaller torus by translates

Fix the selected positive-density lattice. Its covolume is \(V=O(v_d g(R)^d)\), and its minimum vector length exceeds one. Let \(\eta=\varepsilon/4\). A maximal \(\eta\)-separated set \(G\) in the quotient torus is an \(\eta\)-net. Its disjoint torus balls of radius \(\eta/2\) are Euclidean balls of that radius, so
\[
|G|\le\frac{V}{v_d(\eta/2)^d},\qquad
\log|G|\le d\log d+d\log\log d+O(d).
\]
Take \(q=\lceil(\log|G|+1)/p\rceil\) independent uniform torus translations of that one fixed set \(K+\Lambda\). Stationarity of translation gives hit probability \(p\) at every net point. The probability some net point is uncovered is at most \(|G|e^{-qp}<1\). Choose a covering realization. Enlarge each periodic set by an open \(\varepsilon/3\)-neighborhood. The net radius is strictly smaller, so they cover the entire space. Pairs in the old set had distance outside the forbidden band, and the enlargement changes their distance by less than \(2\varepsilon/3\), so they still avoid unit distance. Each enlarged periodic set is the translate of \((K+B(0,\varepsilon/3))+\Lambda\), with a single convex cell per lattice fundamental domain. Assign each point the first covering color for a Borel periodic coloring.

This proves the bound with \(c_*^{-1}=1.84866238\ldots\). The chosen lattice need not have minimum vector length two, so the argument deliberately keeps the cuts from its own translates. The symmetric-cell construction and the covering step remain valid under that choice.

## Verification and literature

The included numerical replay checks the angular prefactor, radial integral and antipodal error bound through dimension 16,384. These are diagnostics. The proof relies on the prior analytical saddle estimate and the cited uniform lattice void theorem. The classical approach to covering by translates has related entropy overhead (see [Naszódi, On Some Covering Problems in Geometry](https://arxiv.org/abs/1404.1691)); the one-cell unit-distance lattice packing geometry above supplies the compact torus and density. No claim on optimality of the \(d\log d\) factor or on historical priority.

## Fixed forbidden intervals

The same construction applies to any fixed \(\ell\geq1\) with forbidden
distance interval \([1,\ell]\). Define
\[
 t_\ell=\frac{\sqrt{\ell^2+8}-\ell}{4},\quad
 g_\ell=(\ell+t_\ell)\sqrt{1-t_\ell^2},\quad
 \alpha_\ell=\frac{t_\ell}{\ell+t_\ell},\quad
 Z_\ell=\frac{1}{\sqrt{(1-t_\ell^2)(1+2t_\ell^2)}}.
\]
Then a one-cell periodic Borel coloring uses at most
\[
 \left(c_\ell^{-1}+o(1)\right)d\log d\,(2g_\ell)^d,\qquad
 c_\ell=Z_\ell^{-1}\max_{\lambda>0}
       \lambda\int_0^1 e^{-\lambda u^{\alpha_\ell}}\,du.
\]
This assertion holds for each fixed \(\ell\), and is not asserted uniformly
in growing \(\ell\), nor claimed to be a best-known bound for general \(\ell\).

Keep \(R=(1-\varepsilon)/2\) and set \(A=\ell+\varepsilon\). The two gap
bounds after enlargement are now less than 1 within a cell and greater
than \(\ell\) between different lattice translates. The relevant vectors
are of length at most \(A+2R=\ell+1\). At \(\varepsilon=0\) the saddle
satisfies \(2t_\ell^2+\ell t_\ell=1\), with \(0<t_\ell\leq1/2\).
The negative second derivative of the log profile is
\((1+2t_\ell^2)/(1-t_\ell^2)^2\), producing \(Z_\ell\) via the same polar
Laplace formula. Its envelope derivative with respect to \(\log r\) at
\(r=1/2\) is \(\alpha_\ell\). Indeed the derivative at a saddle \(t\)
is \(2rt/(A+2rt)\). Since \(g_\ell>\ell\), the antipodal overlap correction
is exponentially negligible for each fixed \(\ell\). The quotient-net
bound has the same leading \(d\log d\); the constant in its \(O(d)\) term
may depend on \(\ell\).

For completeness the optimizer is unique. Put \(s=1/\alpha_\ell>1\) and
\(\gamma(s,\lambda)=\int_0^\lambda v^{s-1}e^{-v}\,dv\). The derivative of
the objective \(s\lambda^{1-s}\gamma(s,\lambda)\) has the sign of
\(\lambda^s e^{-\lambda}/\gamma(s,\lambda)-(s-1)\).
The ratio is the reciprocal of
\(\int_0^1 v^{s-1}e^{\lambda(1-v)}\,dv\), hence strictly decreases from
\(s\) to zero. At \(\ell=1\) these formulas recover the constants above.

## Comparison and replay

[Davies's Section 10](https://arxiv.org/html/2610.12301v1#S10) uses
\(\varepsilon=d^{-1/2}\) and reports an exponential-base result. Retuning
its density calculation and using a much thinner margin on the fixed
cube can itself give \(O(d\log d)(3\sqrt3/2)^d\); the asymptotic order is
not an improvement over that retuned construction. With the same
optimized density and an ordinary small-radius Euclidean net in the
fixed cube, the leading net entropy is \(3d\log d/2\), versus
\(d\log d\) in the single-lattice torus here. This compares this
net-cover route only and is not an optimality assertion about arbitrary
colorings or Davies variants. [Prosanov](https://arxiv.org/abs/1610.02846)
previously used a one-cell lattice packing construction at the older
base 3, and [recent low-dimensional work](https://arxiv.org/abs/2609.20436)
uses Voronoi lattice colorings of a different form.

Run node shell-diagnostics.js for numerical checks at five interval lengths
and six dimensions through 16384. These checks do not establish the
asymptotic result. LatticeShell.lean verifies six supporting real-algebra
lemmas, not Klartag's theorem, the geometric covering construction, or
the Laplace limit. This does not resolve Erdős's question about the
existence or exact value of the high-dimensional chromatic base.

Run python3 antipodal-replay.py for 140 additional exact rational polar-integral checks in odd dimensions 3 through 15.
