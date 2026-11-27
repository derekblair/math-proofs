# Alternative exact rate comparison for the subdivided-K4 Folkman problem

This written supplement replaces the cubic expansion in the geometric proof with exact determinant comparisons. The finite and some matrix ingredients are covered by the Lean files in this dossier. The optimizer and spherical probability argument below are not checked end to end in Lean.

Let H have vertices u,v,x,y,z and edges xy, ux,uy,vx,vy,uz,vz. Let E be an edge, T a triangle, D the diamond on x,y,u,v, and J the graph obtained by attaching one fresh vertex to u,z in H. For a fixed graph F on at most six vertices, let D_F be the maximum determinant among positive semidefinite real matrices with unit diagonal and entries at least t on its edges. Take any sufficiently small fixed 0<t≤1/20000. Write
`f(r)=1−2t²/(1+r)`, `g(r)=1−f(r)` and `I_F=−(log D_F)/2`.

## Localization, clipping, and free entries

The feasible set is compact: each matrix entry has magnitude at most one by its 2×2 principal submatrix. The feasible matrix I+t A_F is positive definite, and in its determinant expansion every term other than the identity has at least two off-diagonal entries. Thus D_F≥1−719t²>0. A maximizer M is positive definite. Its 2×2 principal submatrix at i,j has determinant 1−M_ij²≥det M: reorder those two vertices first and add one remaining row and column at a time, with each Schur determinant factor in (0,1]. Consequently |M_ij|≤27t=:ε for i≠j.

For any selected pair, order it last and write M as `[[A,B],[Bᵀ,C(s)]]`, where C(s) has ones on the diagonal and copies of s off the diagonal. Put W=BᵀA⁻¹B, using the empty matrix convention if no other indices remain. Every entry of W has magnitude at most 8748t². Indeed, for a column b of B, solve Aw=b and use a coordinate where |w_i| takes its maximum. Since |A_ij−δ_ij|≤ε, the equation gives `||w||∞≤ε+(m−2)ε||w||∞` for m vertices. Dotting w with another column of B gives the bound `(m−2)ε²/(1−(m−2)ε)≤8748t²`, using m≤6 and 6ε<1/2. In particular 8748t²<t/2.

Because W is symmetric, the determinant is
`det(A)·[(1−W_00)(1−W_11)−(s−W_01)²]`.
Replacing s by t for a constrained pair, or by W_01 for a free pair, leaves the other entries unchanged and within ε of identity. The replacement remains positive definite: for any vector v and any such symmetric matrix P, `vᵀPv≥(1−mε)∑v_i²`, by the sum of the inequalities `2|v_i v_j|≤v_i²+v_j²`. Thus any constrained entry larger than t or any free entry different from its W_01 would contradict maximality. All constrained entries equal t, and all free ones have magnitude less than t/2.

## The strictly rarer pattern

For a fixed positive definite base correlation matrix A, an added vertex constrained to have correlations at least t with two anchors of mutual correlation r has sharp determinant multiplier f(r), whenever f(r)>0. To see this, express its new column as Aw. With the quadratic inner product from A, let e_i,e_j be the two anchor basis vectors. The choice `w₀=t(e_i+e_j)/(1+r)` has both anchor correlations t and squared norm g(r). If w meets both lower bounds, `⟨w₀,w⟩≥⟨w₀,w₀⟩`. Completing the square proves `⟨w,w⟩≥g(r)`, sharply. The Schur complement is `1−⟨w,w⟩`, and the constructed border is positive definite if the multiplier is positive.

It follows exactly that `D_E=1−t²`, `D_T=D_E f(t)`, and `D_D=D_E f(t)²`: attach the page vertices one at a time to the same saturated edge, with the preceding argument giving both upper bound and construction. The same argument at u,z gives `D_J=D_H f(t)`.

At an H maximizer, let r=M_uv, a free entry with r<t/2. On its diamond submatrix the block on x,y has determinant D_E. Eliminating it leaves a 2×2 Schur block on u,v with diagonal f(t) and off-diagonal r−g(t). Thus that submatrix has determinant at most `D_E f(t)²`. Adding z along u,v multiplies this by at most f(r)≤f(t/2). Consequently
`D_H ≤ D_E f(t)² f(t/2) < D_E f(t)³`.
The comparison is quantitative:
`f(t)−f(t/2)=t³/((1+t)(1+t/2))`. For `L=−(log f(t))/2` and `Δ=I_H−I_T−2L`, this gives
`Δ ≥ −(log(f(t/2)/f(t)))/2 ≥ (f(t)−f(t/2))/(2 f(t)) > t³/4`.
The second inequality uses `−log(1−z)≥z` for `0≤z<1`; all factors are positive.

## Choose the dimension without Taylor expansions

Let `X=L+t³/32` and `d=ceil(log(N)/X)`. The above yields the three necessary strict inequalities
- `I_T−I_E=L<X`.
- `I_H−I_T=2L+Δ>2X`.
- `I_J−I_T=3L+Δ>3X`.

Since `f(t)<1−t²`, one has `I_E<L`. Hence `I_T=I_E+L<3X` for mean triangle growth, and `2I_T−I_D=I_E<2X` for the diamond contribution to normalized variance. Finally `f(t)/(1−t²)=1−(t/(1+t))²`, so the spherical-cap link threshold still has rate `I_eff=L−I_E` and the same link argument applies. Choose t smaller if needed for the spectral estimates. The graph deletion and coloring steps are unchanged.

The usual fixed-pattern Gram-density formula is also stated as Proposition 4(i)–(ii) in the [sample-correlation paper](https://arxiv.org/html/2608.04162v1#S3.SS2). The main proof provides a direct projection derivation and uses [Liu–Mohanty–Schramm–Yang, Theorem 5.1](https://arxiv.org/pdf/2210.00158v1) for the link spectrum. The estimates here do not replace that theorem or assert an explicit finite witness.
