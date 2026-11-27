# Exact short-exchange profiles for bipartite shift graphs and odd quartic grafts

This extends the distance statements in [PR #109](https://github.com/derekblair/math-proofs/pull/109). It gives the full distance-by-component count through the first two cases allowing a second winding, and exact nearest-cycle counts for both distinguished Hamilton cycles in the odd quartic graft. Throughout, cycles and spanning factors are counted as undirected edge sets on labeled vertices. Rotating the graph can produce a different counted edge set.

## The bipartite shift graphs

For \(m\ge D\ge3\), take row vertices \(A_i\) and column vertices \(B_i\), \(i\in\mathbb Z_m\), and edges \(A_i B_{i+s}\) for \(s=0,\ldots,D-1\). Write \(d=D-2\). The distinguished red cycle \(R\) uses shifts \(d,d+1\); other shifts are blue. Distance \(k\) from \(R\) is the number of blue edges added. Define
\[
L(z)=z+z^2+\cdots+z^d,\qquad U(z)=z^2+z^3+\cdots+z^{d+1}.
\]
For \(1\le k<2m/(d+1)\), the number of distinct spanning 2-factors at distance \(k\) that delete exactly \(h\) high-red edges, meaning edges of shift \(d+1\), is
\[
\frac{m}{k}\binom{k}{h}[z^m]\,U(z)^h L(z)^{k-h}.
\]
Such a factor has \(h\) components when \(h>0\), and \(\gcd(k,2)\) when \(h=0\). Consequently the number of Hamilton cycles at distance \(k\) is
\[
m[z^m]\,U(z)L(z)^{k-1}
+\mathbf 1_{k\text{ odd}}\frac{m}{k}[z^m]\,L(z)^k.
\]

Each alternating trail in the difference between the factor and \(R\) winds positively around \(\mathbb Z_m\), using steps \(r-b\in[1,d+1]\), with \(r\) a deleted red shift and \(b\) an added blue shift. Since \(k(d+1)<2m\), there is exactly one trail and its winding is one. Its selected \(A\) vertices are distinct because the steps are positive and sum to \(m\). Its selected \(B\) vertices are also distinct: in cyclic order the positive gap from \(A_i+r_i\) to \(A_{i+1}+r_{i+1}\) is \(r_{i+1}-b_i\ge1\), taking the last gap modulo one full winding. This also proves the converse. Every rooted step word with total \(m\) gives a valid spanning 2-factor, since at each of its distinct selected vertices it replaces one red incidence by one blue incidence. There are \(m\) choices of starting \(A\) vertex. Given the unrooted factor, the alternating trail is unique up to its \(k\) possible \(A\)-roots: each changed vertex has exactly one incident edge of each difference color. Direction is fixed by traversing removed edges from \(A\) to \(B\). Divide by \(k\).

For completeness, contract the retained red path segments in order. The \(i\)th added edge joins segments labeled \(i-\mathbf1_{\{i\text{ low}\}}\) and \(i+\mathbf1_{\{i+1\text{ low}\}}\). Without high cuts these are step-two edges on a cyclic set, with \(\gcd(k,2)\) components. With high cuts, an interval from one high cut to just before the next forms one connected component. The edges at the interval endpoints stay inside by the endpoint formula, and the internal jump-two edges together with the first jump-one edge connect both parity classes. Length one gives a loop and length two gives the first jump-one edge.

The nearest Hamilton distance from #109 is \(k_0=\lceil(m-1)/d\rceil\) and always lies below the second-winding threshold. For \(d\ge1\) this follows from \(k_0\le(m+d-2)/d\) and \(m\ge d+2\), or directly \(k_0=m-1<m\) for \(d=1\). Set \(\rho=k_0d+1-m\in\{0,\ldots,d-1\}\). The nearest count simplifies to
\[
m\binom{k_0+\rho-1}{\rho}+
\mathbf1_{k_0\text{ odd},\ \rho\ge1}\frac m{k_0}\binom{k_0+\rho-2}{\rho-1}.
\]
Indeed \(\rho\) is the step deficit from the maximum word with one high cut, or \(\rho-1\) from the maximum with every cut low. In each case the deficit is at most the per-slot cap \(d-1\), so stars and bars counts it. Cubic examples have exactly \(m\) nearest alternatives. Quartic examples on \(2m\) vertices have exactly \(m\) when \(m\) is odd, and \(m^2/2+2\mathbf1_{m/2\text{ odd}}\) when \(m\) is even. These counts apply to both distinguished quartic cycles by reflection. The whole profile grows beyond these nearest counts. For example, at \(k=\lceil2m/3\rceil-1\) the one-high quartic count is \(\Theta(\sqrt m\,2^{2m/3})\), by the central binomial estimate.

## The odd quartic graft

Use the graft from #109. Replace \(e=A_0B_2\) (red) and \(f=A_1B_1\) (blue) by two-edge paths through the same new vertex. Write \(c_0=A_0B_1\) and \(c_1=A_1B_2\) for the two possible cross-edge suppressions, both of blue shift one. Both distinguished Hamiltons still have nearest distance \(k=\lfloor m/2\rfloor\). Their nearest counts are
\[
(\text{red},\text{blue})=
\begin{cases}
(2,m-1)&m\text{ odd},\\
(2m-2,\ (m/2)(m-2)+2\mathbf1_{m/2\text{ odd}})&m\text{ even}.
\end{cases}
\]

Any nearest Hamilton in the graft suppresses to a nearest base Hamilton, because suppression cannot increase distance and never gives the reference unless it was the reference before suppression. Conversely, lifting a base nearest red Hamilton at the same distance works via \(e\) when it contains \(e\) and omits \(f\), or via a cross edge it contains when it omits both \(e,f\). Lifting via \(f\) increases red distance by one. The cross lift deletes one new blue edge and adds one spoke of each color, preserving red distance. For the blue reference only the lift via \(f\) preserves distance. In particular a cross lift deletes a reference-blue edge and introduces a red spoke, increasing blue distance. Any base cycle containing both \(e,f\) cannot lift as only one deleted edge can be replaced. Different lifts give different two-neighbor choices at the new vertex.

Count the blue lifts by the reflection \(A_i\mapsto A_{-i}\), \(B_j\mapsto B_{3-j}\). They correspond to base nearest red cycles which do not cut the high red edge at \(A_{m-1}\) and do not add the shift-one edge at \(A_0\). When \(m\) is odd, a nearest word has one high step three and every other step two, with no shift-one addition. Its high cut can be any of \(m-1\) allowed positions.

For \(m=2k\), the one-high nearest words come in two types. Type I has high step two and every low step two. It adds its unique shift-one edge at the \(A\) vertex two after the high cut. Type II has high step three, one low step one at position \(j\in\{1,\ldots,k-1\}\) after rooting at the high cut, and every other low step two. Its unique shift-one addition is at relative index \(t=2j+2\pmod m\) measured from the high cut. For each type and each possible \(j\), one high-cut translate is forbidden by \(A_{m-1}\), and a distinct one is forbidden by the shift-one addition at \(A_0\), since \(t\) is even. Thus there are \(k(m-2)\) one-high blue lifts. If \(k\) is odd, two all-low base cycles also lift.

For red lifts at odd \(m=2k+1\), the cut indices relative to the high cut are \(S=\{0,3,5,\ldots,2k-1\}\). Every addition has shift zero, so there are no cross lifts. For absolute high cut \(h\), cutting \(e\) excludes the \(k-1\) even residues in \(-(S\setminus\{0\})\). Adding \(f\) excludes the disjoint \(k\) odd residues in \(1-S\). Two of the \(m\) choices remain.

For red lifts at even \(m=2k\), Type I permits exactly two lifts through \(e\): the high cut is at 0 or at \(m-1\). A cross lift occurs only when the high cut is at \(m-2\) and the shift-one addition is at \(A_0\). The all-low words, when Hamiltonian, have no cross edge and either omit \(e\) or add \(f\), so contribute zero.

For Type II fix \(j\), so the relative cut indices are \(S=\{0\}\cup\{3,5,\ldots,2j+1\}\cup\{2j+2,2j+4,\ldots,2k-2\}\). The relative shift-one addition is \(t=2j+2\pmod{2k}\). To lift through \(e\), the high cut is excluded by either \(-(S\setminus\{0\})\) (cutting \(e\)) or \(1-(S\setminus\{t\})\) (adding \(f\)). These sets have \(k-1\) residues each and are disjoint. For \(j<k-1\), the negative odd part is at least \(2(k-j)-1\), while the odd part of the second set is at most \(2(k-j)-3\). The negative even part is at most \(2(k-j-1)\), while the even part of the second set is at least \(2(k-j)\). For \(j=k-1\), \(t=0\), the negative set is entirely odd and the second entirely even. Thus two lifts through \(e\) occur for each \(j\).

A cross lift requires the unique shift-one edge to be added at \(A_0\) or \(A_1\), with both \(e,f\) omitted. In the \(A_0\) case the relative index of \(A_0\) is \(t\), so \(e\) is cut exactly when \(j<k-1\). Then \(A_1\) is not selected because its relative index \(t+1\) is absent from \(S\). In the \(A_1\) case \(f\) is absent because this edge has shift one, and \(A_0\) is at the low-cut position \(t-1\), so \(e\) is cut for every \(j\). There are therefore \(2k-3\) Type II cross lifts. Adding the three Type I lifts, the \(2(k-1)\) Type II lifts through \(e\), and the \(2k-3\) Type II cross lifts gives \(4k-2=2m-2\).

## Replay and background

The included exact replay enumerates 103,176 non-reference factors across 45 labeled bipartite shift graphs through the applicable boundary, covering 438 nonzero count buckets, 21 exact-second-winding graphs and six one-slack graphs. Its separate literal search covers nine odd quartic grafts and 83,081 Hamilton cycles. Existing transfer-matrix work by [Golin and Leung](https://www.cse.ust.hk/~golin/pubs/golin_WG_04_new.pdf) counts total Hamilton cycles in fixed-jump circulants. The focus here is the number of alternatives at each short exchange distance from a fixed reference, and the asymmetric counts in the odd graft. No priority claim.

## Root extension: exactly at the second-winding threshold
The profile above extends to \(k(D-1)=2m\) by adding \(\binom{g}{2/w}\) to the Hamilton bucket \(h=k\), where g=gcd(m,D−1) and w=(D−1)/g. The strict-threshold one-winding words remain unchanged. In the new weight-2 case every increment has attained D−1, so only shift-(D−1) red edges are deleted and only shift-zero edges are added. No higher winding fits. A factor with only these maximum-increment exchanges is determined by a union of j orbits of addition by D−1 on the row indices: the degree condition at column index i makes A_i selected iff A_{i−(D−1)} is selected. There are g distinct residue orbits of size a=m/g, so there are binom(g,j) such factors at k=ja. Contract the untouched shift-(D−2) red matching. On rows, the exchanged complementary matching becomes the permutation i↦i+1 for unselected residues and i↦i+1−(D−1) for selected residues. It advances residues modulo g by one, and its g-th iterate in each residue layer translates by g−j(D−1)=g(1−jw). Thus the factor has gcd(a,|1−jw|) components. At the threshold jw=2, this is one. This characterization holds for maximum-increment-only factors at any distance; the profile is complete through the exact second-winding boundary, not beyond. When the boundary is an integer, w divides 2, so 2/w is integral.

## Root extension: one unit of slack beyond the second winding
Put s=D−1. When k s=2m+1 (both s and k odd), the full profile still has its one-winding counts and gains exactly m Hamilton cycles with h=k and m with h=k−1. Any winding-two difference has exactly one increment s−1; it is a high-red cut with blue step 1, or a low-red cut with blue step 0. Since gcd(m,s)=1, a separate all-s trail would have length m>k, so the difference is a single winding-two trail. Root at the unique defect. With root A_0, its selected A sites in traversal order are x_0=0 and x_i=i s−1 mod m for 1≤i≤k−1. They are distinct: s is invertible and the unique index solving i s≡1 mod m is k, outside the range. The B sites for low defect are (i+1)s−1 mod m, all distinct. For high defect only B_0 differs (it is s, not s−1), and collision would again require i s≡1 with 1≤i<k. Thus each defect type and root gives a valid distinct factor, m possibilities per type.
Write k=2a+1, s=2b+1, m=a s+b. The circular red order of the A cut sites in their traversal labels is [0,a+1,1,a+2,2,…,2a,a]: compare the arithmetic progressions i s−1 and j s−b−1 after reduction. This is addition of a+1 mod k. The red order of cuts is the same for either type, because the low vs high edge at an A site is immediately before vs after it on red. For all high cuts, label each surviving red segment by the cut after which it begins. In the difference trail, the blue edge from the removed B endpoint at label i to the next A endpoint has segment endpoints i and i+1−(a+1)=i−a, giving one cycle because gcd(k,a)=1. If cut 0 is low, its A endpoint is on segment 0 instead of previous segment a and its B endpoint on segment a instead of 0. The contracted graph replaces edges 0→a+1 and 2a→a by edges a–(a+1) and (2a)–0. In the single cycle with oriented step −a, the first replacement joins the two heads and the second joins the two tails of the removed edges, so the two remaining paths rejoin into one undirected cycle. This also covers k=3 where one path may be a single vertex. Therefore all 2m winding-two factors at one slack are Hamilton.

The accompanying Lean file verifies four supporting arithmetic lemmas: there are only one or two windings in the stated range, equality of the capped increment sum saturates every step, the second-winding interleaving inequality holds, and the maximum-increment accumulated step is exactly minus one layer. The full graph bijections, component counts and odd-graft formulas are written arguments, not Lean theorems.
