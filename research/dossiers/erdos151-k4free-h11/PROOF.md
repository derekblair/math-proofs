# The K4-free H=11 case of Erdős #151 (proof)

**Strongest statement:** If a K4-free graph on at least 47 vertices
is edge-(3,3)-Ramsey, then its free-set parameter beta is at least 11.
The three-stage containment argument below needs only Bikov's
minimum-degree theorem for a minimal Ramsey core and elementary
small Ramsey upper bounds. It does not assume a previous H=10 result,
Seymour, the purely triangular case, or the locally-Wagner enumeration.
The full conjecture and general K4-containing cases remain open.
The proof is independently audited and verified end to end in Lean. No literature-priority claim is made.

Write beta(G) for the largest set containing no whole maximal clique
of size at least two. In a K4-free graph, these forbidden sets are
triangles and lone edges (edges in no triangle). Suppose n≥47, G is
K4-free, beta(G)≤10, and C is a minimal edge-(3,3)-Ramsey subgraph.
In particular Delta(G)≤10 because every open neighborhood is free.
By [Bikov, Theorem 8.2](https://arxiv.org/abs/1604.03716), each core
vertex has degree at least eight in C. Every core edge lies in at
least two triangles of C: otherwise a good coloring of C minus that
edge extends by choosing an available color for the lone triangle.

**Main new lemma.** No vertex w of C has degree 10 in G. The proof
uses β≤10 and the ambient/core degree conditions only, not the
initial Ramsey jump or local price reduction.

## Unblocking count

For contradiction set S=N_G(w), |S|=10, r=d_C(w)≥8. S is free:
no triangle in a K4-free link, and its own edges all make triangles
with w, hence are not lone. Let X be the n−11 vertices outside S
and w. For x∈X write s_x=|N(x)∩S| and ℓ_x for the number of those
connecting edges which are lone in G. Since beta(G)≤10, every x has
a blocker in S: either one connecting lone edge or a triangle with
two vertices of S. Thus s_x≥1.

Call x **private to u** ∈S if (S−u)+x is free. Any original
blocker must use u, so every such x is adjacent to u. If distinct
private x,y are nonadjacent, (S−u)+x+y is free: each lone edge or
triangle would have to be in one of the one-vertex extensions,
or contain both x and y, which would require their adjacency.
This contradicts beta≤10. Therefore the private vertices of u
form a clique in N(u), hence number at most two. Moreover if any
of them joins u by a lone edge then there can be only one:
a second private vertex would complete a triangle on that lone edge.

Let a,b,c,d respectively count exterior vertices of these types:
    (s,ℓ) = (1,1), (2,0), (2,1), (2,2).
All exterior vertices with s≤2 have one of these types. The first
type gives one private incidence along the lone edge. The second
type gives two, since its one possible triangle is a blocker and
it has no lone edge. The third gives one private incidence along
its lone edge: these two common neighbors could not form a blocker
triangle since the edge is lone. The fourth gives no required
private incidence. The a+c lone-private incidences have distinct
owners in S, each with its private capacity reduced to one.
Counting private incidences gives a+2b+c ≤ 20−(a+c), so
a+b+c≤10. Also total ℓ=Σℓ_x is at least a+2d.

Write I=Σ_x s_x. Every other exterior x has s_x≥3. Hence
    I ≥ 3(n−11) − 2a − b − c − d
      ≥ 3(n−11) − 10 − a − d
      ≥ 3(n−11) − 15 − ℓ/2.
The final inequality uses a≤10 and a+2d≤ℓ.

Among the ten vertices of S, r are neighbors in C and have core
degree ≥8, so each has at most two ambient lone edges in total.
The other 10−r vertices have at most nine edges to X, since w
uses one slot. Thus ℓ≤2r+9(10−r)=90−7r. Counting common-neighbor
incidence over the r core edges from w, the induced graph G[S]
has at least r edges (each core edge w–u has ≥2 triangles in C).
Each edge inside S uses two degree slots and each edge to w one,
so I≤90−2r. Combining inequalities gives
    I ≥ 3(n−11) − 60 + 7r/2 ≥ 48+7r/2
      > 90−2r  (r≥8).
The minimal deficit at n=47,r=8 is exactly two. Contradiction.

## Unconditional endpoint: exclude ambient degree 9

Use the same S=N(w) but with ambient degree d=9 and r=d_C(w)≥8.
We already know **every** core vertex has ambient degree at most 9.
There are n−10 outside vertices. Define U to be the ones already
unblocked by S, meaning S+x is free; put z=|U|. These vertices form
a clique: a nonadjacent pair could jointly join S, giving a free 11-set.
Thus z≤3. For every u∈S use the same private set as above, but only
among originally blocked vertices. Private vertices all neighbor u.
Any three independent private vertices could join S−u (size 8),
giving a free 11-set. Indeed a forbidden clique can include at most
one member of any independent group, and every one-vertex extension
is safe. So the private set has independence at most two; it sits in
the triangle-free link of u, and R(3,3)≤6 implies size at most five.

Any private vertex attached by a lone edge at u is isolated in the
induced graph on private vertices of u. If there is one such vertex,
the remaining private graph has independence at most one, hence it
is a clique in a triangle-free graph, of size at most two. If there
are two lone private vertices they are the only private vertices;
three is impossible. In particular for each u,
    2·(#private) + 3·(#lone private) ≤ 10.
Classify only the blocked vertices with s≤2 into a,b,c,d as before.
Their contributions to this weighted private capacity imply
    5a+4b+5c ≤ 90.
As ell≥a+2d, their deficit below three incidences each satisfies
    4(2a+b+c+d) ≤ 90 + 3ell.
The unblocked vertices need not be isolated; safely drop their
incidences for a lower bound. It follows
    4I ≥ 12(n−10−z) − 90 − 3ell.
For each of the r neighbors belonging to C via w, ambient degree
is at most nine and core degree at least eight, so it has at most
one ambient lone edge. Any of the other 9−r neighbors has at most
nine exterior edges. Consequently ell≤81−8r. At least r edges
lie inside S and the core neighbors have one fewer total slot than
the ambient maximum (10). Thus I≤81−3r. At n≥47 the lower bound
is 4I≥75+24r whereas the upper is 4I≤324−12r, contradictory for
r≥8 (gap at least 39).

## Exclude ambient degree 8 and conclude

Now all core vertices have **exactly** eight ambient and eight core
neighbors. At such a w, S=N(w) has eight vertices; each in S is
a saturated core vertex, so there are no lone edges incident to S.
The unblocked set U cannot have three independent vertices (would
give a free 11-set with S), and G[U] is K4-free. Thus z≤8 by
R(3,4)≤9. Even the elementary upper R(3,4)≤10 suffices (z≤9).
Private vertices among the blocked ones, for fixed u, can have no
independent 4-set, since |S−u|=7; their induced graph is triangle-free
as a subset of N(u), so each private set has size at most eight
(or nine with R≤10). Every blocked x has s≥2, because a lone edge
is unavailable. If s=2, its unique triangle blocker forces x
private to both neighbors. Hence at most 8·8/2=32 blocked vertices
have s=2 (or at most 36 with R≤10). All other blocked x have at
least three incidences, so I≥3(n−9−8)−32≥58 (weaker 51).
But I≤8·7−2·8=40 because each S vertex has degree eight and at
least eight edges lie inside S. Contradiction.

Consequently no core exists. In a K4-free graph with H(n)=11 one
has n≥47 by Exoo's R(3,11)≥47 bound. If beta≤10, any good edge
2-coloring would give a red-plus-lone triangle-free spanning
subgraph meeting every ambient maximal clique (all triangles and
lone edges), hence a free independent 11-set, impossible. Thus
there would be a minimal edge-Ramsey core, which was just excluded.
This proves Erdős #151 for every K4-free G with H(n)=11, not the
unrestricted statement or all K4-free cases. The n≥47 edge-Ramsey
theorem also implies beta≥11 whenever H(n)≥11, which is not the
sought larger H(n) bound when H(n)≥12.
