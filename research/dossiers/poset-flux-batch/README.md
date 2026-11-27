# Exact batched pair, triple and quadruple order counts in posets

For an \(n\)-element poset with a supplied \(w\)-chain partition and an
ideal DAG of \(J\) states and \(E\) arcs, the arithmetic bounds below
include writing the complete table of ordered counts:
* pairs: \(O(n^2+\min\{wE,Jn^{\omega-1+\epsilon}\})\);
* triples: \(O(n^3+\min\{w^2E,Jn^{\omega(1,1,2)-1+\epsilon}\})\);
* quadruples: \(O(n^4+\min\{w^2E^2+JE,n^2wE\})\), without fast matrix
  multiplication. In particular the width-two bound is \(O(n^4)\), the
  size of the explicit table, and the width-three bound is \(O(n^5)\).
The exponents \(\omega\) and \(\omega(1,1,2)\) concern respectively square
and \(n\times n\) by \(n\times n^2\) multiplication over the rationals.
All \(O\)-bounds with an \(\epsilon>0\) hold for each fixed \(\epsilon\).
It suffices to substitute \(\omega+1\) for the rectangular exponent by
ordinary column blocking. The bounds do not improve counting the total
number of extensions alone.

## Common representation

Habib, Medina, Nourine and Steiner's [Theorem 6](https://doi.org/10.1016/S0166-218X(00)00258-4)
constructs the labeled ideal covering DAG in \(O(J+E)\) time and space
beyond the supplied adjacency representation. Add input read cost if
needed. A spanning tree from the empty ideal (choose one incoming arc
per nonempty ideal) permits a walk that updates one chain-prefix length
per step. Store prefix vectors if streaming the outputs by pivot;
this costs \(O(wJ)\) words and time, within the sparse bounds.
The separate threshold-based sparse replay is also described by the
following direct implementation: preprocess, for each vertex and chain,
the deepest direct predecessor position. In an ideal, checking direct
predecessors suffices to add the next element of a chain. BFS enumerates
only feasible prefix vectors, and a deterministic trie with balanced
children permits \(O(w^2J\log(n+1))\) preprocessing and indexing for that
implementation. This is not needed for the stronger published-DAG bound.

Each linear extension is a path through this DAG from empty to full.
Write \(F(I)\) and \(B(I)\) for the standard prefix/suffix path counts.
The edge \(e:I\to I+y\) has weight \(F(I)B(I+y)\), the exact number of
extensions using that edge. All edges with label \(y\) partition all
linear extensions. Compute them with two sweeps of the DAG.

## Pairs and triples

For pairs, an edge labeled \(y\) contributes its weight to \(N(x<y)\)
exactly for \(x\in I\). In concatenated chain order that is a union of
at most \(w\) disjoint prefixes. Add the weight to each prefix with two
signed difference writes; one prefix sum per row recovers the counts.

For triples \(N(x<y<z)\) the same edge contributes when \(x\in I\) and
\(z\notin I+y\). This is a union of \(w^2\) disjoint prefix-by-suffix
rectangles, each updated at four corners and recovered with two prefix
scans. Process each pivot \(y\) separately for \(O(n^2+wJ+E)\) working
words apart from streamed output. The same stencil works in fixed
dimension for specified sets all before or all after one pivot, not
for arbitrary multi-pivot orders.

Alternatively form \(A[y,I]=F(I)B(I+y)\) for legal edges and zero otherwise.
Let \(H[I,x]=\mathbf1_{x\in I}\). Then \(AH\) gives pairs. For triples
multiply by \(H'[I,(x,z)]=\mathbf1_{x\in I}\mathbf1_{z\notin I}\)
and zero all entries with \(z=y\). The other repeated-label cases
are already zero. Block over \(n\) ideals at a time and pad the final
block. Constructing the incidence rows costs \(O(Jn)\) for pairs and
\(O(Jn^2)\) for triples, absorbed in the respective arithmetic bounds.
The dense branch uses its own multiplication workspace; it is not
asserted to have the sparse streaming memory bound or bit complexity.

## Quadruples and scope

See poset-quadruple-flux.md for the two elementary methods. A pair of
middle edges factors into prefix paths, connecting paths, and suffix
paths. Compute connecting-path tables by ordinary forward sweeps, and
range-add the outer pair by rectangles. Alternatively propagate, for
each fixed first pair, prefixes that already realize that pair and
suffix-add at every third edge. The methods require neither a fast
matrix multiplication routine nor an approximation.

For exact integer implementation, each fixed pivot's edge, or fixed
middle labels' edge-pair, partitions a subset of all extensions. Counts
and weights are bounded by \(n!\), and signed accumulators have
\(O(n\log(n+1))\) bits. For pairs, with \(L=O(n\log(n+1))\) and multiplication
cost \(M(L)\), the sparse arithmetic bit cost is
\(O(E M(L)+(n^2+wE)L)\) apart from indexing; analogous substitutions apply
to triples and the sparse four-way methods. A supplied deletion set of
size \(k\) leaving width two yields \(J\le 2^k(n+1)^2\) by representing
each deleted vertex as its own chain, so all pair output is computed
in \(O((k+2)^2 2^k n^2)\) arithmetic operations given the structure.
No new worst-case bound for unstructured extension counting is claimed.
In the unrelated worst-case model, [Oka v2](https://arxiv.org/abs/2608.19505v2) counts extensions in O*(33^(n/6)) time with exponential space. Adding a fixed pair comparison and counting again retains that exponential base for the whole pair table. [Kozma and Tan](https://arxiv.org/abs/2611.23653) give an O*(2.829^n) polynomial-space baseline. Our improvement is sensitive to the actual ideal DAG and supplied chain partition.

[De Loof–De Meyer–De Baets](https://doi.org/10.3233/FUN-2006-712-309)
give \(O(Jnw)\) for all exact mutual-order counts on the same ideal DAG
in their model, and a separate forward/backward DP. The gain is
replacing per-edge scans over the selected elements by at most \(w\)
range updates (or by blocked incidence multiplication for dense
instances). This is not a claim to be the first quadratic algorithm
on width two. [Blocking ideals](https://arxiv.org/abs/2501.11073) are
related exact pair-counting methods. Neither this comparison nor the
live Google cross-check establishes historical priority.

## Reproducibility

Run the included Node replays for sparse pair, block pair, both
quadruple methods, and dense/rectangle triple checks. They compare
BigInt tables with literal extension enumeration, check repeated
labels and empty rectangles, and do not benchmark fast multiplication.
The independent pair sparse replay has 1,600 cases and the dense pair
replay has 900. Both four-way methods replay 480 cases, testing 832,704
entries each. The triple script checks literal and batched products.
FluxRectangles.lean verifies finite difference recovery, not the full
enumeration or asymptotic complexity proof.
