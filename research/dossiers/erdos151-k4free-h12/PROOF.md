# Proof of the K4-free H(n)=12 case

Write β(G) for the largest free vertex set, where free means it
contains no whole inclusion-maximal clique of size at least two.
In a K4-free graph the forbidden sets are the triangles and the
lone edges (edges not belonging to any triangle). The complement of
a free set meets every forbidden set. We prove β≥12 when H(n)≥12.

**Red-plus-lone and an auxiliary bound.** In a coloring with no
monochromatic triangle, retain red edges and all lone edges. This
spanning subgraph is triangle-free, and every forbidden set contains
one of its edges. Its independent sets are free in G. The public
(3,12)-Ramsey witness on 52 vertices also proves n≥53, by restriction
to smaller vertex sets.

The only external Lean premise is [Angeltveit's published
R(3,10)≤41](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v32i4p30).
It supplies a free ten-set for any colorable K4-free graph of order
at least 41 by the preceding red-plus-lone argument. For a noncolorable
one, suppose β≤9. A minimal Ramsey core has minimum degree eight and
at least two triangles on each edge. Every open neighborhood is
free, so Δ≤9. At an ambient degree-nine core vertex, the private
pool charging argument below, with free cap nine, gives
`12(n−10) ≤ 4I+54+2ell`. With `I+2r≤72` and `ell+7r≤72`,
the right side is at most 310, impossible for n≥36. At remaining
degree-eight core vertices the neighborhood is all in the core,
no lone edge crosses it, and I≤40. At most three exterior vertices
are unblocked, and each owner has at most five private vertices;
thus `6(n−12)≤2I+40≤120`, also impossible. This proves the needed
free-ten bound for n≥41 using R(3,10)≤41. A free set in an induced
remainder is still free with respect to the original graph.

**Minimal core and safe pair insertion.** Suppose now G has β≤11
and no good coloring. Take an edge-minimal Ramsey core C. Its
nonisolated vertices have core degree r≥8, every core edge has
at least two core triangles, and [Bikov's marked-link
atlas](https://arxiv.org/html/1604.03716v1#S8) applies at core
degree eight. Ambient Δ≤11. For adjacent core hubs u,v, remove
their c ambient common neighbors, all lone-edge attachments, and
the complement of an independent set in each remaining exclusive
neighbor pool. The exact safe price is
`q=d(u)+d(v)−2−c−alpha_u−alpha_v`, where alpha_u and alpha_v are
the independent sets retained in the respective eligible pools.
If q≤n−43, insert both hubs into a free ten of the remaining at
least 41 vertices. Hence `d(u)+d(v)≥n−40+c+alpha_u+alpha_v`.

Every pool is nonempty: the second core triangle on an edge to a
common neighbor supplies an eligible exclusive neighbor because the
ambient common neighbors are independent. Each pool has at least
`r−1−c` vertices on its side. Triangle-free Ramsey bounds now give
`c+alpha_u+alpha_v≥6`. A budget at most six forces c=2 and r=8
on both sides. A budget at most seven permits c=2,3,5 only, with
c=5 requiring both r=8 and both pools of independence one. Such
pools have at most two vertices, so all five ambient common neighbors
are common in the core, forbidden by the maximum degree four of
Bikov's degree-eight links.

**Incidence exclusions at n≥53.** Let S=N_G(w), r=d_C(w), X the
exterior (not S or w), I the S–X incidence count, ell the lone
incidences, and e the number of edges in the core link. The preceding
pair budgets strengthen as n grows. Ambient d≤7 is impossible;
d=8 would give only ambient-11 core neighbors with codegree two and
hence r=8,e=8, below the atlas minimum ten. At ambient d=9, any core
edge has codegree at most three, so e≤13 when r=9. At any r=8 the
atlas gives e≤12.

At ambient d=11 all exterior additions are blocked. Classify small
supports by (number of S neighbors, number of lone S neighbors):
a,b,c,d count types (1,1),(2,0),(2,1),(2,2). Every other blocked
vertex has at least three incidences. A private vertex becomes
insertable after removing its owner from S. For each owner private
vertices form a clique in its triangle-free link, with at most two
and at most one if there is a private lone edge. Hence a+b+c≤11.
Also a≤11 and a+2d≤ell≤3r+10(11−r). It follows that
`I≥3(n−12)−11−(a+d)`, and a+d is at most 29,25,22 for r=9,10,11.
Comparing with `I≤110−2e` gives e≤13,11,10 at those respective
degrees.

At ambient d=10 an owner has a private pool of independence at
most two. Its size p is at most five; if q of the private vertices
are attached by lone edges they are isolated in the pool, and
`2p+3q≤10`. For an exterior blocked vertex the four types above
require at least (1,1),(2,0),(1,1),(0,0) private and private-lone
owners, respectively. Thus `a≤20`, `5a+4b+5c≤100`, and
`a+c+2d≤ell`. With `δ=2a+b+c+d` we obtain
`4δ≤100+a−3c+2ell≤120+2ell`, with `ell≤100−7r`.
The z unblocked vertices form a clique, so z≤3. If their edge is
non-lone it must have a witness in S to block adding the pair.
When z=3 these witnesses are distinct at each unblocked vertex
by K4-freeness, so their incidence contribution I_U≥6. For z=2
and a non-lone edge, I_U≥2. We have
`I≥3(n−11−z)−δ+I_U` and `I≤100−2e`.

For r=10 this gives e≤14. At r=9 it gives e≤13 except the potential
e=14 equality: n=53, z=2 with a lone joining edge, I_U=0, and
δ=48. The scalar constraints leave (a,b,c,d)=(19,1,0,9) or
(20,0,0,8). The first is impossible: nine owners already have two
isolated private vertices filling independence two, but b needs
two distinct extra owners. In the second each owner has two
single-lone A leaves. Either unblocked vertex must meet one such
leaf per owner by a lone edge (otherwise insert it after replacing
that owner with both leaves). The choices are disjoint because the
unblocked pair has a lone joining edge. They saturate degree
eleven. Pick any double-lone D with owners s,t. Remove s,t from S
and insert D, the two A leaves at s,t in the same layer, and the
unblocked vertex of the other layer. The four new vertices are
independent and anticomplete to the retained part of S. This
gives free twelve, a contradiction.

**Density and coloring.** We have shown `2e≤3r` at every core
vertex, strictly when r≥9. For an edge-minimal Ramsey graph, its
triangle hypergraph has a minimally non-bicolorable subfamily
using every graph edge. The classical [critical hypergraph density
bound](https://doi.org/10.1093/qmath/25.1.303) gives T≥E. Indeed,
if a minimally non-bicolorable hypergraph had more vertices than
edges, a nonzero null vector of the incidence matrix would give
both signs on any hyperedge touching its support, and the remaining
edges could be colored by minimality. Combining 3T=Σe and 2E=Σr
forces r=8,e=12 everywhere. Two atlas rows survive. One is cubic
Wagner; the other has two low (degree two) and two high (degree
four) points, each low adjacent to exactly the same high pair.
An edge of codegree two between vertices of the second type gives
them the same high pair, by symmetry of the common-neighbor set.
Following its two low neighbors forces one high vertex to have
three edges of codegree four, impossible in either surviving type.
Thus all links are Wagner.

A direct Hall argument then colors the core. Its triangle–edge
incidence graph is cubic bipartite. A cut of size at most five
has at most three mixed host vertices: each mixed link charges
at least three split incidences, and each incidence is counted at
most twice. The host stays connected after deleting those vertices
because a Wagner link stays connected after deleting two vertices.
Thus the minority side has at most three graph-edge nodes, all
inside the at-most-three mixed host vertices. A Wagner link
square gives an incidence 8-cycle whose four triangle nodes have
distinct outside third edges. Delete that cycle. A Hall deficit
would give sides S,T with |S|>|T|, crossing counts a,b with
`a−b=3(|S|−|T|)`, `a≤4`, `a≤|S|`. Its cut has size at
most five and its internal incidence at least |S|+|T|. The
complement cannot be the minority (it contains four square
spokes), and the minority S,T can contain at most |T|+2 internal
incidences, a contradiction. Hence a matching can alternate on
the incidence 8-cycle. Contract matched pairs, orient
arcs from each matched edge toward the other edges of its
triangle, and alternate colors on the resulting directed 4-cycle.
Balanced degrees and connectedness give directed reachability
to that cycle. Color vertices oppositely to a successor closer
to the cycle. Every triangle gets both colors, contrary to
the choice of core.

The known alternating-matching/directed-cycle mechanism is
related to [Choi–Kwon–Park, §3](https://arxiv.org/html/2609.33902v1#S3)
and [Strong edge-colourings of truncations of cubic graphs,
§3](https://arxiv.org/abs/2610.41950v2). Earlier
[locally Wagner work](https://erdosproblemaday.com/day/151-k10-the-core-is-locally-wagner)
obtains the required colorability by classification. No priority
claim is made for these prerequisites. The new arguments are
the two-hub and incidence reduction at the H(n)=12 threshold,
and the direct cut certificate for the Wagner step in the
formalization.
