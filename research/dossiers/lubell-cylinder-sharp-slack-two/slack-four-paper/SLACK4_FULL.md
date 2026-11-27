# Proposed complete slack-four Lubell optimum (paper proof; not Lean-verified)

Let t,u be positive integers, t≤u and u≥2, n=t+u+4. Write w_i=1/C(n,t+i),
A=C(u+4,2), B=(t+2)(u+2)+1, C=C(t+4,2)≤A. Then the exact Lubell maximum
is the larger of the following two displayed, admissible constructions:

* Low construction: a fixed t-set and all ≤2-site extensions on the other
  u+4 sites. Score L = w_0+(u+4)w_1+A w_2.
* Balanced product: left block t+2 with at least t+1 points, right block
  u+2 with at most one point. Score P = (t+2)w_1+B w_2+(u+2)w_3.

This is Wu–Feng Problem 1.3 at excess four, not the usual cardinality
product problem. It uses the classical Complete Intersection Theorem of
[Ahlswede–Khachatrian (1997)](https://doi.org/10.1006/eujc.1995.0092).
The geometric upper bound is a written proof with independent review,
not yet Lean-verified. No priority claim is made.

## Which construction wins?

Write d=u−t. Dividing by the positive center weight w₂, the difference is

  2(t+1)(L−P)/w₂ = (t+3)d(d+5) + 14 − t³ − 4t² − t.

This is increasing for d≥0. At d=t−1 it is 2(t+1)²; at d=t−2
it is −4(t+1). Thus the optimum is strictly L if u≥2t−1
and strictly P if t≤u≤2t−2. For t=1 only the first alternative
applies. The scaled polynomial comparison is verified separately
in `Threshold.lean` with only the three standard axioms. This Lean
file does not prove the geometric upper bound.

## Families with either outer layer

If a t-set belongs to the family, every set contains it and
[the bottom analysis](SLACK4_BOTTOM.md) proves the bound L. If a
(t+4)-set belongs to the family, every set is its subset. Pass to
complements, so the extra set size is at most four on t+4 sites, with
weights in reverse order. Four-element extras force the four-site
cylinder, already bounded. A family with no triples is at most
w_4+(t+4)w_3+C(t+4,2)w_2≤L, using t≤u, w_4≤w_0 and w_3≤w_1.

If it has f distinct triples, let c be the number of eligible pairs.
For a fixed triple pattern on the t+4 sites, its normalized difference
from L, after omitting the nonnegative (w_0−w_4)/w_2, is
  (u+4−f)(u+3)/(t+2) − (t+4)(t+3)/(u+2) + C(u+4,2)−c.
Here f≤max(t+2,4)≤u+4 by the Johnson star/top dichotomy. All three terms
are nondecreasing with u≥t, fixing t and the triple pattern. When t≥2 the
difference is strictly positive already at u=t by the bottom analysis
and symmetry. For t=1 its first permitted u is 2, with f≤4 and c≤9
on the five sites, hence the displayed expression is at least
2·(5/3)−5+(15−9)>0. Thus the upper outer layer also implies the bound L.

## Families with no outer layer

Let α, μ, β denote the layer counts in sizes t+1, t+2, t+3 respectively.
The center is a t-intersecting family of (t+2)-sets. CIT gives
μ≤max(A,B,C)=max(A,B), the sizes of its i=0,1,2 threshold families.
If both α,β≤3 and μ≤A, use 3w_1+3w_3≤6w_1≤(u+4)w_1 to bound by L.
If both counts ≤3 and μ≤B, use α≤t+2 and β≤u+2 to bound by P.

Suppose α≥4. The Johnson star/top description applies to the lower adjacent
layer since any pair of (t+1)-sets meet in at least t.

1. **Star case.** Its α members are a common t-core T plus α distinct
   single-site extensions. A member A of any higher layer that does
   not contain T must contain exactly t−1 core points and all α leaves
   (otherwise one of the t-intersections fails). No center can do this:
   its size t+2 is too small. If all upper adjacent members contain T,
   add T and use the outer-layer bound. Otherwise α=4, and an exceptional
   upper adjacent member misses one core site and has all four leaves.
   Each center contains T and needs intersection ≥t+1 with this
   exceptional member (use the union bound), so both its extra sites
   must lie among the four leaves: μ≤6. Each ordinary upper adjacent
   member (containing T) needs intersection ≥t+2 with that exceptional
   member, so all three of its extras lie among the four leaves: at most
   4 ordinary members. An exceptional member is determined by the
   missing site in T, so β≤t+4. Thus the weighted score is at most
   4w_1+6w_2+(t+4)w_3. To compare with L, divide the difference by w_2,
   omit w_0/w_2>0, and obtain
     u(u+3)/(t+2) − (t+4)(t+3)/(u+2) + C(u+4,2)−6.
   This is increasing in u; at u=t≥2 it equals
   C(t+4,2)−6−4(t+3)/(t+2)>0 (first case t=2, monotone afterward).
   At t=1,u=2 it is also positive.

2. **Top case.** The α members are formed by omitting one of at least
   four distinct sites from a common J with |J|=t+2. Every center or
   upper adjacent member meets J in at least t+1; otherwise to meet
   each lower member in t it would have to miss all the α omitted
   sites of J but could miss at most two. Hence centers are J or a
   one-site swap, giving μ≤B. If all upper adjacent members contain J,
   then β≤u+2 and we are bounded by P. If some upper member Y misses a
   site j of J, it contains two outside sites. For any center swapping
   out i≠j and swapping in an outside site not in Y, the intersection
   with Y is t, too small for the union bound. Exactly (t+1)u
   geometrically possible centers of this form are forbidden. Thus
   μ≤B−(t+1)u. The upper layer alone has β≤max(u+2,t+4) by applying the
   Johnson star/top theorem after complements. Relative to P at most
   two extra upper members occur, and (t+1)u·w_2≥4w_2>2w_3
   (w_3/w_2≤5/4). This again bounds by P.

Finally suppose α≤3 and β≥4. Apply the geometric analysis of sections
1 and 2 after complementing the whole family and interchanging t,u;
the geometric counts did not require a parameter order. In its star
case either we can add the complementary core (reduces to the outer
case), or β=4 and μ≤6. At most 3w_1+6w_2+4w_3≤7w_1+6w_2 is then
bounded by L: u≥3 is immediate, while u=2 uses w_1/w_2≤5/3 and A−6=9.
In its top case the common-J argument always gives μ≤B and β≤u+2,
whereas α≤3≤t+2, so no potential opposite layer count excess arises and
the score is at most P.

Cases exhaust all families. The two displayed constructions give the
matching lower bound. An independent exact maximal clique search in
the original weighted set graph confirms (t,u)=(1,2),(1,3),(2,2),(1,4),
(2,3) (ground sizes 7–9), with maxima 6/7, 3/4, 27/70, 2/3, 5/18.

A separate exact enumerator did not use compression or the Complete
Intersection Theorem. Its original-graph search also checked all three
admissible ordered pairs at n=10: (1,5) gave 3/5, (2,4) gave 2/9, and
(3,3) gave 19/126. This is a cross-check, not a substitute for the proof.
