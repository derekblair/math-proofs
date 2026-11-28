# Supplied feedback set on the relevant shortest-path union

For strictly positive lengths on a directed graph, the union of the
full shortest-path edges for k required pairs can be computed by two
Dijkstra passes per pair. The concatenation of attained minima and a
candidate arc under the distance equality cannot repeat a vertex: a
repetition would give a positive-length closed subwalk which could be
removed to obtain a shorter route. Thus the edge test is exact even
without a topological order. Individual source-tight graphs are
acyclic, but their union need not be. If the union is acyclic, run the
DAG algorithm on that union to get the retained-size bound.

Otherwise suppose a supplied set F of f nonterminal vertices has an
acyclic complement in the union. For fixed k≥3 and f, assign each F
vertex to one path or leave it unused, and order the visited vertices
along each path. Guess the entering and leaving arcs at each visited
vertex. Parallel arcs can be replaced by one lightest representative
when the output is a witness for vertex-disjointness; this need not
preserve the identities of all tied parallel copies. Verify connector
consistency for consecutive F vertices joined by one arc, and do not
count that arc twice. There are O_{k,f}(n^{2f}) branches. A nonadjacent
connector pair defines an outside fragment by its two outside endpoint
vertices; the fragment is a singleton if these coincide. The initial
and final outside pieces have the original terminals as their outer
endpoints. Include the full path for a pair visiting no F vertices.

Any shortest witness in the union induces one such branch; all its
outside pieces are minimum between their endpoints in the common
acyclic complement. Otherwise substituting a shorter outside piece
would give a shorter walk, and then a shorter path after removing any
positive cycles. Reject inconsistent branches, overlaps of fragment
terminals across separate fragments (including singleton fragments),
unreachable fragment destinations, and branches in which the sum of
each path's outside minima and fixed distinct connector arc lengths
differs from that pair's original minimum. For an accepted branch,
the disjoint DAG fragments plus the distinct assigned F vertices
glue to vertex-disjoint shortest paths of the original pairs.
Repeated vertices within the same concatenation are disallowed by
the same global fragment disjointness check.

There are between k and k+f outside fragments before dropping
singletons. One can retain singleton pairs via the same isolated dummy
terminal treatment where needed; alternatively delete every forced
singleton from the live graph and pad to k pairs with isolated zero
pieces, then check the original distance sums. Calling the reporting
algorithm on common input G*−F (or its filtered version) gives total
expected Õ_{k,f}((m+n)n^(k+3f−2)) in the same arithmetic model.
Approximate false-negative probability only needs to be bounded on
one fixed feasible branch; all returned candidates are valid. No
subroutine finds F, and this is not a runtime claim for general cyclic
instances. The reduction and time accounting are paper, not Lean.
