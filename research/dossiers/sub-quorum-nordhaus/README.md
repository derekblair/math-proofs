# The exact complementary upper bound for sub-quorum colorings

For every simple graph G with n vertices,
`psi_sq(G) + psi_sq(complement(G)) <= n+2`.
The bound is attained for each n >= 2 by the empty graph and its complement.
This proves Ma, Sahbi, and Zhang's Conjecture 9.2 in
[Sub-quorum colorings of graphs](https://arxiv.org/html/2609.25128v4#S9),
using their partial-coloring and weak-majority convention in Definition 2.2.

## Proof sketch

Start with any onto partial coloring of each graph. Build a bipartite
incidence graph on the disjoint union of the two palettes. Every original
vertex colored on both sides witnesses an edge between its two colors.
An original vertex colored only once belongs to the component of its
single color; a doubly colored vertex belongs to the common component.
Vertices colored neither way do not contribute.

In each connected component, let r be the number of assigned original
vertices and k the number of colors. The incidence component has at least
k-1 simple edges, and each edge has a distinct original-vertex witness,
so k <= r+1. If k>r, equality forces all r original vertices to be
doubly colored. Call such a component positive. Surjectivity ensures
that all palette components have at least one assigned vertex.

Fix an original vertex x in a positive component of size r. All its
same-colored neighbors on either side are in its own component. Those
neighbor sets are disjoint, because one uses edges of G and the other
edges of the complement. Together they contain at most r-1 vertices.
Every doubly colored original vertex outside the component is in a
different color from x on both sides. It is an other-colored neighbor
on exactly one side. Each of the two quorum inequalities allows at
most one more other-colored neighbor than same-colored neighbors.
Thus there are at most r+1 doubly colored vertices outside this component.

If there were three positive components with sizes a, b, c, applying
this bound to them gives b+c <= a+1, a+c <= b+1, and a+b <= c+1.
All three sizes must then be one. For their three original vertices,
every vertex has at most one neighbor in G and also at most one neighbor
in the complement within the triple. This would give every vertex
degree exactly one in a graph on three vertices, which is impossible.
Therefore at most two components are positive, each by only one.
Summing across components gives the bound.

For sharpness, in the empty graph give every vertex its own color.
In the complement color two distinct vertices with two private colors
and leave the remaining vertices uncolored.

## Formal verification

* `QuorumIncidence.lean`: component counts, injection of incidence edges
  into original vertices, and positive components are doubly colored.
* `QuorumNordhaus.lean`: exact equivalence with the closed-neighborhood
  definition and the bound for any two admissible colorings.
* `QuorumMaximum.lean`: finite maximum and the exact theorem
  `QuorumBounds.conjecture9_2`, plus `QuorumBounds.sharp_on_empty`.
* `quorum_nordhaus_check.py`: independent exhaustive partial-partition
  checks on every labeled graph of orders 2–5 and 80 larger controls.

Use Lean 4.27.0 and Mathlib v4.27.0 (commit
a3a10db0e9d66acbebf76c5e6a135066525ac900). Set MATHLIB_DIR to a cached
checkout of that version, then run `bash check.sh` and
`python quorum_nordhaus_check.py`. The exact theorem uses only standard
Lean axioms; no native evaluation is used in the proof.

## Priority and scope

The versioned article states this upper bound as open. Targeted author,
title, and conjecture searches and the accompanying
[public repository](https://github.com/the-omega-institute/subquorum-colorings)
found the known earlier hypercube resolution, not a solution of this
complementary bound. This is a bounded literature check, not an absolute
priority assertion. The separate grid conjecture and lower extremum
are not addressed here.
