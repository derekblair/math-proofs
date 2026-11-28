# Independent box-DP audit

Source checked: Cao–Qi–Wang arXiv:2611.34013v1, especially §3
(capped source distances), Lemma 9.3 (level averaging), §11 Q11.1
and Q11.2. This proof uses actual solution arcs, not their
configuration holding/width relation.

Let X_a(v)=π_a(v)−π_k(v), a<k, and interpolate linearly on
actual solution segments. On a commodity-i shortest arc all
own differences y_{ij}=π_i−π_j increase weakly. Set
φ_i=Σ_{j≠i}y_{ij}. Since X_a=y_{ik}−y_{ia}
(with y_{ii}=0), change in X_a on any portion of such a
segment is bounded absolutely by the change in φ_i. Any two
points in a box of longest side W have all pair-coordinate
differences bounded by 2W. For one path in its vertex order,
the clipped segment intervals in that box have nonnegative
φ_i increments with sum at most the span of φ_i across the
first and last clip points, ≤2(k−1)W. This does not require
the geometric path to meet the box in a connected interval.

A cut at an interior level c of a longest coordinate sees
each clipped segment's projected interval (discard finitely
many endpoints/coplanar levels). The average over the middle
third is at most 6k(k−1). Crucially count all clipped actual
segments, even segments with both endpoints outside the box.
A solution arc leaving a descendant's box meets at least one
face; that face either is original (strict root margins
prevent exits) or originated in a previous split and lies
inside the box to which its averaging bound applied. Charge
it to one such face, obtaining boundary size ≤12k(k−1)^2.
An outgoing arc grazing a corner still crosses at least one
of the coordinate halfspaces of its exited faces; no selected
input vertex lies on the planes. Boundary refers to endpoints
belonging/not belonging to the same box vertex subset, not
to every segment which intersects its boundary.

Use nested actual geometric boxes including during any unary
cuts; never replace them by tight input ranges in the proof.
Longest sides decrease by factor ≤2/3 when selected, so within
at most k−1 cuts any old max width drops by ≥ factor 2/3.
If two distinct positions persist, finitely many such steps
must eventually give a binary cut. Skip no-change unary
nodes in the *rank-indexed algorithm*, since their geometric
subsets are identical. The subsequent genuine split on one
coordinate partitions that same subset in the same way.
The algorithm enumerates finite ranks, not the number of
geometric unary cuts; coordinate ratios do not enter runtime.

One state stores the directed labeled arcs with one endpoint
in the vertex subset, size O(k^3). Interiors must satisfy exact
local indegree/outdegree (source out only, sink in only,
internal either unused or one of each in a single commodity).
Initially remove any zero-length commodity only after
reserving its vertex and computing all original shortest-path
DAGs; deleting its vertex when building other paths must not
alter what lengths count as shortest. If distinct commodities'
terminals coincide, reject. A binary transition compares exact
unordered sets of shared crossing arcs (including direction
and commodity); nonshared outside arcs equal parent boundary
restrictions. Children are disjoint vertex domains. Gluing
cannot create a disconnected component of used vertices with
no source/sink, since that would be a directed cycle in the
strict commodity-i shortest DAG. Degree conditions then leave
exactly the desired single path per commodity.

For a tied-position leaf the union of commodity DAG arcs is
itself acyclic: all pair differences are constant, so every
allowed arc increases π_1 by its positive weight, even when
π_1 is capped. Create internal fragment starts from demands
with remaining out-degree but no in-demand, ends conversely.
Reserve any vertex with both a prescribed external input and
output (its internal fragment is length zero), plus all target
zero-length commodities. Invalid boundary incidence conflicts
are rejected. Enumerate same-commodity start/end pairings
and solve their explicitly arc-constrained disjoint paths by
the standard DAG token DP: reserve every fragment terminal
against other fragments; advance the currently earliest
unfinished token in a common strict topological order; once
it leaves a vertex, all other unfinished tokens are later.
Completed terminal remains reserved. At most O(k^3) fragments.
There are at most n^{O(k)} box rank states and n^{O(k^3)}
arc assignments/pairings/token states; crossing match checks
polynomial. Treat parallel arcs by keeping a minimum-weight
representative and remove positive loops (or include m as an
explicit input size for preprocessing). For k=1 use ordinary
shortest paths. This gives n^{O(k^3)} in the same positive-real
weight arithmetic/comparison model. No width guarantee for
arbitrary configurations and no answer to Q11.2.

## Sharpened quadratic exponent

The preceding cubic bound can be sharpened by retaining only the two
own differences that enter the chosen coordinate. Fix the axis j,
and write X_j=y_{ik}−y_{ij} on a commodity-i segment. Both y terms
are monotone even on the clipped subintervals. The box range of
y_{ik}=X_i is at most W (zero for i=k), and that of y_{ij}=X_i−X_j
is at most 2W, taking X_k=0. For each of the two functions, order
the nonempty clipped segments along the solution path and sum
their increments; intervening gaps contribute only nonnegative
increments, so each sum is bounded by the function range. The
summed variation of X_j is therefore ≤3W per commodity, not
2(k−1)W. The longest-axis middle third gives ≤9k crossings
per selected face. There are ≤2(k−1) faces, hence all boundary
states can be restricted to B=18k(k−1) arcs.

The tied leaf has at most B+k nonzero fragments. Their at-most
(B+k)! pairings are n^{O(k²)} because k≤n, and the same exponent
bounds all token-state searches, even without an optimized
matching argument. There are n^{O(k)} rank boxes and both
children's states can be combined by a Cartesian product without
changing the n^{O(k²)} class. This independently checks the
sharpened n^{O(k²)} answer to Q11.1's first bound.
