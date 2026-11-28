# H=13 low-price three-hub deletion: unified n≥64 paper proof

This supersedes the separate marked-owner-triangle n≥65 closure.
The n=65 argument is still useful as a different general exchange
mechanism. This does NOT address possible H=13 orders 61–63.

Assume G K4-free has n≥64, β≤12, maximum degree≤12, and contains
an edge-minimal edge-(3,3)-Ramsey core C. As before use Bikov's
minimum degree 8 and degree-eight marked atlas. From H10 and
Angeltveit's R(3,10)≤41 there is a free10 in every K4-free pool
of least 41 vertices; from H11 and Goedgebeur–Radziszowski's
R(3,11)≤50 there is a free11 in each pool of at least 50.
Induced-free always implies ambient-free.

## Exact three-hub geometry

Let x,w,y be an ambient induced path with both edges core.
Set c1=|N(x)∩N(w)|, c2=|N(y)∩N(w)|, C=c1+c2, and let
t=|N(x)∩N(w)∩N(y)|. Set
s=|(N(x)∩N(y))−({w}∪N(w))|, so c(x,y)=1+t+s.
Let D=d(x)+d(w)+d(y)≤36.
The union of hub neighborhoods after excluding the hubs themselves
has size D−4−C−s: their two path edges account for four oriented
within-hub incidences, and inclusion-exclusion gives the stated
intersection discount. A free set inserted with all three hubs
is safe after removing every outside vertex adjacent to both
endpoints of either path edge, every lone attachment to a hub,
and conflicts among the retained vertices of each hub's link.
The path itself contains no forbidden blocker (both internal
edges are non-lone).

There are two disjoint retained pools:
1. Eligible center-exclusive neighbors of w, which therefore
   attach to neither outer hub. This pool provides at least
   max(0,r_w−2−C+t) available vertices (counting only core edges
   at w), and its induced graph is triangle-free.
2. Eligible outer neighbors from the two ambient sides outside
   N(w)∪{w}. As with two nonadjacent hubs, give these vertices
   a conflict edge only if they are ambient adjacent and both
   neighbor at least one common outer hub. This graph is
   triangle-free, since there is no conflict edge between a
   vertex exclusive to x and one exclusive to y.
   Counting original core-exclusive candidates of x,y gives at
   least (7−c1)+(7−c2) incidences. For any of the s common outer
   vertices the total loses at most one: two core contributions
   mean both attachments are non-lone and at least one copy
   remains; one contribution can lose at most itself. Thus there
   are at least max(0,14−C−s) available outer vertices.

Independent subsets in these pools combine without additional
conditions, even if the ambient graph joins them: no pair of
vertices from different pools shares a hub. Let α_total be the
sum of these two retained independent-set sizes. Deletion q is
at most D−4−C−s−α_total. It suffices to retain 12−C−s vertices
(count at least zero) to have q≤20. With three hubs set aside,
at least 41 vertices remain, and a free10 gives free13.

## Which path yields the budget

This selection is used when w has core degree nine and its
core link has e≥14. We seek one of these actual ambient patterns:
(A) c1≥4 and c2≥4; or
(B) c1≥4, c2≥3 and t≥2 (interchanging outer hubs allowed).

If C+s≥10, the required retention is at most two. The available
outer pool of size≥14−C−s suffices by triangle-freeness: four
vertices guarantee two independent, three guarantee at least one.
For smaller C+s, all cases are below.

* C+s=7: necessarily C=7, s=0, pattern (B) has c1,c2=4,3.
  Since s=0 the exclusive pools are fully disjoint and wholly
  nonlone, of sizes at least three and four, each yielding two.
  The center count r_w−2−C+t≥2 gives another one.
* C+s=8: when C=7,s=1, outer count≥6 gives three and center
  contributes one. When C=8,s=0, split c1,c2=4,4 gives 2+2;
  split 5,3 gives 1+2 and a center vertex (t≥2 in pattern B).
* C+s=9: when C=7,s=2, outer count≥5 gives two and center one.
  When C=8,s=1 and c1,c2=5,3, same argument applies. When C=9,s=0,
  permitted splits 4,5 or 6,3 give 2+1, since the outside-common
  set is empty. The only extra case is c1=c2=4,s=1. Each core
  candidate pool sizes ≥3. If the single shared ambient vertex
  belongs to at most one of the core pools, discard it and
  choose one from the potentially diminished pool (≥2) and two
  nonadjacent from the other (≥3). If it belongs to both, it
  is eligible and each exclusive side has ≥2 candidates. If
  either exclusive side has a nonadjacent pair, choose it plus
  any vertex of the other side. Otherwise select an adjacent
  pair on each side and take the shared vertex and one
  nonneighbor of it from each pair; the nonneighbors exist by
  triangle-freeness of each side.

Thus either pattern gives a safe triple insertion at n≥64.

## Finding the two pivots

Let H be the *ambient-induced* graph on the nine core neighbors
of w, not just the core link. It is triangle-free, has minimum
degree≥2 (each core spoke has at least two core triangles), and
has at least 14 edges. We claim H contains a nonadjacent pair
of vertices both having degree at least four, or a nonadjacent
pair of degrees ≥4 and 3 sharing at least two neighbors.
This gives (A) or (B) above; importantly these vertices are then
actually nonadjacent in G. For a maximum-degree pivot x, let
U consist of its nonneighbors other than itself. Triangle-free
gives N(x) independent, so e(H)=d(x)+Σ_{y∈U}d(y)−e(H[U]).
If no pair of nonadjacent degree≥4 vertices exists, every
vertex in U has degree≤3. For d(x)≥6 we would have
e(H)≤d(x)+3(8−d(x))≤12, impossible. For d(x)=5, e(H)≥14
forces all three vertices of U to have degree three and
e(H[U])=0; each shares three neighbors with x. For d(x)=4,
if every degree-three y∈U had at least two neighbors inside U,
then Σ_U d ≤ 8+k and e(U)≥k with k=#degree-three vertices,
giving e(H)≤12. Thus some degree-three y has at most one neighbor
inside U and shares at least two with x. Finally Δ(H)≥4 by
e(H)≥14 on nine vertices. The claim follows.

Consequently n≥64 does not permit positive link surplus at
*any* core-degree-nine vertex, even if its ambient degree is 12.

## All other rows, and conclusion

For r=8 the marked atlas gives e≤12 directly. For ambient d≤10,
each adjacent core edge has budget at most seven since n≥64
and the other endpoint has d≤12. The previous pair argument
then forbids genuine codegrees above three. If r≥10, the only
budget-seven option has c=2, so 2e=2r<3r (strict); r=9 already
handled above.

For ambient d=11 and r≥10, put S=N(w), exterior X of size
n−12≥52, and let U be the unblocked exterior set. It is a clique
of size z≤3 because two unblocked nonadjacent vertices could
join S to give 13. If z=3 the three vertices form an ambient
triangle; as in the H12 proof, each of its pairs is non-lone
and must have a common blocking neighbor in S. Each of its
three vertices has at least two distinct witnesses (otherwise
K4), so U contributes ≥6 incidences. In every case the three
incidences-per-blocked-column baseline plus unblocked
contribution is at least 150.

Use the H12 d10 private-owner argument with S size11 and
β≤12, so each private pool still has α≤2 and bound
2p+3q≤10. If a,b,c,d are the counts of small blocked columns
(s,l)=(1,1),(2,0),(2,1),(2,2), this gives a≤22,
5a+4b+5c≤110, a+c+2d≤L. Thus aggregate deficit
δ=2a+b+c+d satisfies 4δ≤110+a−3c+2L≤132+2L.
Lone incidence slots give L≤4r+11(11−r). For r=10,11
one gets δ≤58,55, respectively. Thus I≥92,95, and
I+2e≤11·11=121 gives e≤14,13. These are strict density deficits.

For ambient d=12 use the ordinary saturated-owner d12 argument
from PROOF.md: if Sp is the amount of single- and double-lone
columns then I≥3(n−13)−12−Sp, I+2e≤132, and
2Sp≤144−7r. At n≥64 for r=10,11,12 this gives respectively
2e≤28,24,21, strictly below 3r.

Now every vertex has 2e≤3r, strictly if r≥9. Global Seymour
critical triangle-incidence bound forces equality; all core
vertices have r=8 and e=12. The already checked marked #2 low/high
obstruction leaves locally Wagner; the constructive Wagner
colorability proof excludes such a core. Therefore every
K4-free edge-(3,3)-Ramsey graph on n≥64 has β≥13. The colorable
red-plus-lone branch gives the maximal-clique transversal claim
when H(n)=13 at these orders. This is a paper proof, not yet a
Lean formalization of the new three-hub step.
