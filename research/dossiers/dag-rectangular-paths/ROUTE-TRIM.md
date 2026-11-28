# Relevant-arc preprocessing for exact DAG shortest-path reporting

For each required pair (s,t), use one forward and one reverse topological
distance pass, allowing negative lengths and ties. An unreachable required
pair makes the instance infeasible. Keep u→v if for at least one pair
the two endpoint distances are finite and d_s(u)+w(u,v)+d_t(v)=d_s(t).
Retain all terminals, including terminals of zero-edge routes, and remove
unneeded other vertices. Costs are arithmetic/comparison counts for exact
weights, the same model as the original DAG result.

The retained arc criterion is exact. If equality holds, concatenate
an attaining prefix, the arc, and an attaining suffix. These form a
route, with no repetition because topological ranks strictly increase.
Conversely, the pieces of any minimum route bound the two distances
from above, and concatenating attaining pieces gives a full route,
bounding the stitched cost from below by the minimum. The full-route
union keeps all tied routes for every pair. Taking a subgraph with
unchanged edge lengths cannot create any other minimum route. Thus
it preserves all feasible disjoint path tuples. For the main algorithm,
recompute its source-tight masks on this graph as a fresh common input;
there is no claim for arbitrary per-commodity masks.

For fixed k the resulting reporting cost is O_k(m+n) plus the smaller
applicable compact-graph bound; the sparse term is
Õ_k((m*+n*)n*^(k−2)). A dense example consists of disjoint chains of
unit-cost diamonds and all other forward arcs with weight > n. The
retained graph has linear size and still exponentially many tied paths.

Lean independently checks the route split/concatenation, edge test,
topological simplicity and exact union preservation in FullRouteTrim.lean.
This is not an executable Lean distance algorithm, a full formalization
of the reporting algorithm, or a new bound for all dense inputs. The
two-distance characterization is elementary; the corollary only refines
the input-size analysis of the existing sparse result.
