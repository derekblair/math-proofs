# Optimal density and barriers for a random Euclidean coloring construction

[Davies, Theorem 1.5 and §10](https://arxiv.org/html/2610.12301v1#S10) builds random periodic sets avoiding unit distance and obtains a coloring upper bound \((3\sqrt3/2+o(1))^d\). We determine the optimal expected density in its basic independent-center model, and show that two classes of asymmetric cuts cannot improve its exponential coverage rate. These results describe the construction, not the chromatic number of Euclidean space. The [exact open limit question](https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/FormalConjectures/ErdosProblems/704.lean) remains open here.

## Model and statement

Take \(N\) independent uniformly distributed centers in the torus with period \(2\mathbb Z^d\), and work with all their periodic copies. Let \(0<\varepsilon\le 1/4\), \(A=1+\varepsilon\), and \(R=(1-\varepsilon)/2\). At each center \(a\) retain offsets \(x\) with \(\|x\|<R\) and \(x\cdot u<(s-A)/2\) for every other center copy at \(a+su\), \(s>0\), \(\|u\|=1\). These sets are disjoint: for points \(a+x,b+y\) in two distinct pieces their difference has projection \(>A\) along \(b-a\). A center's own translated copies are too far away to cut its open ball. Let \(\rho_{d,N}\) be the expected density of their union.

Define
\[
g(r)=\max_{0\le t\le1}(A+2rt)\sqrt{1-t^2}.
\]
Uniformly for \(0<\varepsilon\le1/4\) and large \(d\),
\[
\sup_{N\ge0}\rho_{d,N}\asymp (R/g(R))^d ,
\]
with absolute constants. If \(\varepsilon=\varepsilon_d\to0\), the ratio to \((R/g(R))^d\) converges to
\[
c_*=\frac{3\sqrt2}{4}\max_{\lambda>0}3\lambda\int_0^1 t^2 e^{-\lambda t}\,dt .
\]
The quadrature sanity check gives \(c_*\approx0.54093\). For the original \(\varepsilon=d^{-1/2}\), \((R/g(R))^d=(2/(3\sqrt3))^d\exp(-4\sqrt d/3-16/27+o(1))\). The leading density base for this random model is therefore \(2/(3\sqrt3)\).

## 1. Intensity exact formula, angular saddle and torus projection

For an offset \(x\) of length \(r\), its forbidden displacement region \(F(x)\) has radial function \(A+2rt\), with \(t=u\cdot x/r\) (use a constant radius if \(r=0\)). Write \(F_T(x)\) for the measure of its projection onto the period-two torus, and \(V=2^d\). Disjointness of retained pieces and independent uniform competitors give exactly
\[
\rho_{d,N}=\int_{\|x\|<R}\frac NV(1-F_T(x)/V)^{N-1}\,dx,\qquad N\ge1.
\]
No conditioning on successful cells is needed.

Writing \(v_d\) for unit-ball volume and \(c_d=\Gamma(d/2)/(\sqrt\pi\,\Gamma((d-1)/2))\), polar integration gives
\[
 |F(x)|/v_d=c_d\int_{-1}^1\alpha(t)^3 [\alpha(t)\sqrt{1-t^2}]^{d-3}\,dt,\qquad
 \alpha(t)=A+2rt .
\]
The maximum is at the unique interior saddle \(t_*\in[0,1/2]\) satisfying \(2r-At_*-4rt_*^2=0\). This also holds at \(r=0,t_*=0\). The second derivative of \(\log(\alpha(t)\sqrt{1-t^2})\) is \(- (2r/\alpha(t))^2 -(1+t^2)/(1-t^2)^2\le-1\); it is also bounded below on the fixed band \(|t-t_*|\le0.05\), uniformly over these parameters. With \(c_d\asymp\sqrt d\), integration of this Gaussian upper envelope and of a band of width \(d^{-1/2}\) give \(|F(x)|\asymp v_d g(r)^d\).

In fact \(F_T(x)=(1-O(e^{-c d}))|F(x)|\), uniformly in the direction of \(x\) and in the same parameter range, for some absolute \(c>0\). The mass outside \(|t-t_*|\le0.05\) is exponentially small by the preceding Gaussian envelope. Inside that band write \(u=t\widehat x+\sqrt{1-t^2}v\), where \(v\) is uniform on the unit sphere in \(\widehat x^\perp\). Uniform spherical tails in that \((d-1)\)-dimensional subspace and a union bound show \(\max_j|v_j|\le0.04\) except with exponentially small probability. This is uniform in \(\widehat x\) because each coordinate projection onto the subspace has norm at most one. As \(|t|\le0.55\) and \(\alpha(t)\le1.25+0.75(0.55)=133/80\), every \(su\) in this part has coordinates of absolute value at most \((133/80)(0.55+0.04)<1\). It is in the open cube of side two, on which the projection is injective. The uniform statements at \(r=0\) follow by choosing any reference direction.

## 2. Optimize over the number of centers

For \(N\ge2\), \(N(1-F_T/V)^{N-1}/V\le2/(eF_T)\) by \(z e^{-z}\le e^{-1}\); for \(N=1\), \(1/V\le1/F_T\). Furthermore \(\frac{d}{d\log r}\log(r/g(r))\ge 1/2\): by the envelope calculation \(\frac{d}{d\log r}\log g=2rt_* /(A+2rt_*)\le 1/3\) for \(0<r\le R\). Therefore integrating against radial volume bounds the density by a constant times \((R/g(R))^d\). In the opposite direction pick \(N\) of order \(V/(v_d g(R)^d)\), with a sufficiently small absolute constant. The uniform angular upper bound and monotonicity of \(g\) make survival at least \(1/2\) by a union bound, uniformly in offsets, and the integral is bounded below by a constant times \((R/g(R))^d\). The ratio \(V/(v_d g(R)^d)\) tends to infinity by Stirling.

To obtain the actual prefactor if \(\varepsilon_d\to0\), the boundary saddle tends to \(t_*=1/2\), \(\alpha(t_*)=3/2\), and \((\log g(t))''=-8/3\), where here the derivative is of the angular profile as a function of \(t\). The Laplace prefactor in the polar integral is \(4/(3\sqrt2)\). More explicitly the uniform Gaussian bounds above dominate the angular integral after the substitution \(t-t_*=u/\sqrt d\); the rescaled integrand converges to its Gaussian with that second derivative and \(c_d/\sqrt d\to1/\sqrt{2\pi}\) by Stirling. This argument also applies when \(r=R x^{1/d}\) for any fixed \(x\in(0,1]\). The ratio \(F_T(R x^{1/d}\widehat x)/(v_d g(R)^d)\) therefore tends to \((4/(3\sqrt2))x^{1/3}\), uniformly in \(\widehat x\) for each such \(x\), by the envelope derivative, which tends to \(1/3\) there.

Set \(p_d=|F(R)|/V\to0\), where the Euclidean forbidden volume at radius \(R\) is direction-independent, and \(\lambda=(N-1)p_d\). Use the volume-coordinate \(x=(r/R)^d\). For bounded \(\lambda\) converging to a limit, dominated convergence gives the normalized density limit \((3\sqrt2/4)\lambda\int_0^1 e^{-\lambda x^{1/3}}dx\). Large and small \(\lambda\) do not optimize: the angular estimates and logarithmic derivative bound give \(F_T/V\ge c p_dx^{1/3}\); hence for large \(\lambda\) the normalized density is bounded by a constant times \((\lambda+p_d)\int_0^1 e^{-c\lambda x^{1/3}}dx=O(\lambda^{-2})\). The small-\(\lambda\) bound is \(O(\lambda+p_d)\). The mesh \(p_d\) tends to zero. Substitute \(t=x^{1/3}\) to get the claimed supremum limit. Its unique positive maximizer satisfies \(4e^\lambda=\lambda^3+2\lambda^2+4\lambda+4\) (after dividing their difference by \(\lambda^3\), the sign has exactly one positive crossing). Finally at \(\varepsilon=0\) the boundary value is \(g=3\sqrt3/4\); differentiating \(\log g(R)\) with \(R=(1-\varepsilon)/2\) gives first derivative \(1/3\) and second derivative \(5/27\), by the saddle equation. Subtract the derivatives of \(\log R\) to get the stated expansion at \(\varepsilon=d^{-1/2}\).

## 3. Two asymmetric variants and the final enlargement

Give each center an independent mark from one fixed probability law, and allow smaller marked radii at most \(R\). A shifted cut is \(x\cdot u<(s-A)/2+h(a,b,s,u)\), where \(a,b\) now denote the two marks. Always require \(h(a,b,s,u)=-h(b,a,s,-u)\), so opposite cuts preserve the same gap and the retained pieces are disjoint. The two cases below make separate assumptions, not assumed to hold for arbitrary mixtures of the two.

**Unoriented rules.** Suppose \(h\) depends on the length and the unoriented direction (in particular it is even in \(u\)), so it is antisymmetric in the marks for every displacement. Fix \(x\) and choose a measurable representative for each point of its original symmetric forbidden torus region, independent of marks (choose the first in a fixed ordering of the finitely many possible representatives). A competitor with \(h\le0\) at that representative certainly removes \(x\). Let \(D(a)\) be the probability of this sign event, averaged over a uniform point of the forbidden region and over the opponent mark. If \(E\) is a set of marks of mass \(v\), antisymmetry gives \(\int_E D(a)\,d\mu(a)\ge v^2/2\) by exchanging marks restricted to \(E\times E\). Hence \(\Pr(D\le t)\le2t\), including at \(t=0\). Conditional survival is at most \((1-pD(a))^{N-1}\) for \(p=F_T/V\). Averaging gives at most \(2/((N-1)p)\) for \(N\ge2\), by integrating the distribution function against the exponential kernel. Multiplication by \(N/V\) and angular integration yield the same upper bound up to an absolute constant as for symmetric cuts. Dropping smaller-radius constraints and cuts from other copies of one's own center only helps the upper bound.

**Odd directional rules.** Instead suppose \(h\) is odd in \(u\), independent of \(s\), and bounded in magnitude by a fixed constant independent of dimension. It can vary with both marks subject to cut consistency. For fixed focal mark \(a\), let \(F_a(x,z)\) be the average Euclidean forbidden volume when the shifts are multiplied by scalar \(z\):
\[
 F_a(x,z)=v_d\,\mathbb E_{b,u}\left[(A+2(x\cdot u-z h(a,b,u)))_+^d\right].
\]
It is convex jointly in \((x,z)\), and \(F_a(-x,-z)=F_a(x,z)\) by oddness. Thus \(\int_{\|x\|<R} e^{-\lambda F_a(x,z)}dx\) is log-concave by [Prékopa's marginal theorem](https://acta.bibl.u-szeged.hu/14411/) and even, and is maximized at \(z=0\). The projected forbidden measure of any particular competitor at \(z=1\) is at least its Euclidean forbidden volume divided by a polynomial in \(d\): the region is contained in a ball of fixed radius \(2+2\sup|h|\), so any two representatives differ by a period vector with bounded squared integer norm and only polynomially many are possible. Use this lower bound on the projected measure in the survival probability, ignore own nonzero copies, and take \(\lambda=(N-1)/(V\,\mathrm{poly}(d))\) for \(N\ge2\). Prékopa bounds the resulting radial integral by the one at zero shift. Optimize the same pointwise exponential upper bound as above, costing only another polynomial. For \(N=1\), the density cannot exceed the uncut ball density, which is smaller than the stated exponential bound. Thus odd directional rules cannot improve the leading exponent either.

Finally the open \(\delta\)-neighborhood of any retained set is contained in the relaxed model on the very same centers and shifts, with \(R'=R+\delta\), \(A'=A-2\delta\). Every old distance-to-cut inequality can worsen by at most \(\delta\). At Davies's \(\delta=\varepsilon/3\) this is exactly the relaxed choice \(\varepsilon'=\varepsilon/3\). The leading density ceiling survives enlargement, but the precise raw prefactor is not asserted for enlarged sets. For any \(k\) random classes with these marginals, irrespective of dependence between classes, covering a fixed grid (or the entire torus) implies covering one fixed point. Stationarity and the union bound give coverage probability at most \(k\) times the one-class expected-density ceiling. Constant-success schemes in these models therefore need at least \((3\sqrt3/2-o(1))^d\) classes. This does not bound exceptional deterministic placements, correlated within-class center processes, arbitrary cut rules, or the true chromatic number.

## Verification and limits

The replay checks 2,058 exact scalar/lattice identities and numerically checks the angular, radial and optimal-intensity formulas through dimension 2,048. Numerical checks are diagnostics, not certificates for the analytical limit. Lean checks six supporting scalar identities and inequalities, not the measure, polar integrals, Prékopa argument or the full theorem.
