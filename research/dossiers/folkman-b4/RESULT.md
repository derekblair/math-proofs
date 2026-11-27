# The four-page book Folkman question: a proof draft

**Target.** [Xu, Liang and Radziszowski, Problem 3.1](https://arxiv.org/pdf/1705.06268) asks whether the generalized edge Folkman number \(F_e(K_3,K_3;B_4)\) exists. The answer asserted here is **no**: if every edge of a finite simple graph lies in at most three triangles, then its edges have a red/blue colouring with no monochromatic triangle. This also answers the \(k=4\) case of their Problem 3.2, but not the other cases. No \(K_4\)-free assumption is used.

**Verification boundary.** This is an independently reviewed written proof using published matching theory. Lean verifies the two forbidden-configuration arguments with actual unordered edge endpoint sets. The full hypergraph/matching/brace composition below has not been formalized in Lean. No first-public-proof or repository CI claim is made.

### 1. Reduce to a positive Pfaffian cubic incidence graph

Suppose the desired colouring fails. Take an inclusion-minimal non-two-colourable family of triangles. Form a triple system with these triangles as lines and the graph edges they use as points. Its incidence graph is connected by minimality. Its points have degree at most three.

For any matrix with positive entries at the incidences and zero elsewhere, a nonzero real kernel vector would give a proper partial colouring: colour its nonzero coordinates by sign. Every row meeting the support has both signs, because the weighted sum is zero with positive coefficients. The proper subfamily of rows avoiding the support can be coloured by minimality, and this colours the unused coordinates without conflict. Thus every such matrix has trivial kernel. In particular the number of lines is at least the number of points. The opposite inequality follows by counting incidences, since lines have size three and points have degree at most three. Equality forces every point to have degree three.

The matrix is therefore square and sign-nonsingular. If two perfect matchings in the cubic incidence graph gave determinant terms of opposite signs, assigning weight one on the first matching and small positive weights elsewhere would give the first sign, and the same construction at the second would give the opposite sign. Continuous interpolation through positive weights would contradict nonsingularity. Thus all perfect matchings have the same permutation sign. In particular no 4-cycle is *central* (has a perfect matching after its four vertices are removed), since its two alternating matching choices have opposite signs.

### 2. Find a Heawood fragment

Use the standard structure of bipartite matching-covered graphs: a brace is one with no nontrivial tight cut; in the simple case on at least six vertices it is 2-extendable. A tight cut is a cut crossed by exactly one edge of every perfect matching. Every edge of a cubic bipartite graph lies in a perfect matching, by decomposing it into three perfect matchings via Hall's theorem.

If the incidence graph is already a brace, use it directly. Otherwise take an inclusion-minimal nontrivial tight shore \(S\), and contract its complement to a vertex. This produces a matching-covered brace: any nontrivial tight cut of the contraction would, on its side excluding the contracted vertex, give a strictly smaller nontrivial tight shore of the original. This follows by restricting each original perfect matching to the contraction. All tight-cut edges face the same way in the bipartition, since the signed imbalance of the two classes of \(S\) is fixed and every cut edge is in a perfect matching. Regularity now shows the cut consists of three edges and the contraction is cubic. The shore has odd size and cannot have size three: one class would have two vertices, and its unique vertex on the other side has all three original, distinct neighbours inside the shore. Thus the contraction has at least six vertices. It is simple, since a parallel pair would yield distinct-neighbour degree at most two, excluded by the bipartite brace Hall condition at that order.

The contraction is Pfaffian, by the standard inheritance across tight cuts. For this case, a direct sign argument is also available: for each possible contracted-port edge, fix a perfect matching of the original complement shore using that edge. Two perfect matchings of the quotient choosing that port differ only by alternating cycles inside \(S\). Their lifts show the signs agree. Independently sign each port edge to equate the three resulting sign classes.

By [Gorsky, Johanni and Wiederrecht, Lemmas 3.3 and 3.4](https://arxiv.org/html/2408.08128v3), a non-Heawood simple Pfaffian brace of this order has two edge-disjoint 4-cycles. In a cubic graph they are vertex-disjoint, so one avoids the contraction vertex. Every 4-cycle of a brace is central: extend two opposite edges to a perfect matching. If contracted, the matching off the square lifts to the original graph by choosing any perfect matching on the complement shore with the same cut edge. This gives a central 4-cycle in the original, impossible. Thus the brace is the Heawood graph, the incidence graph of the Fano plane.

The original graph of incidences consequently contains the full Fano plane, a Fano plane minus a line, or a Fano plane minus a point. In the last case, each dangling line vertex still has its actual third point outside the shore.

The Pfaffian route is classical. An earlier alternative uses [Funk, Jackson, Labbate and Sheehan, Theorem 2.2 and Lemma 4.9](https://webspace.maths.qmul.ac.uk/b.jackson/detext.pdf), and the Fano-leaf connection independently appears in the [knotlab Fano-leaf proof draft](https://github.com/jscul/knotlab/blob/main/proofs/THREEFOLD-GRAMMAR-20261030-001A/THREEFOLD-GRAMMAR-20261030-001A-P001_fano_leaves_and_planar_glue/proof.md). The argument here does not require that draft as a theorem. For bibliography see [Seymour (1974)](https://doi.org/10.1093/qmath/25.1.303) and [Robertson, Seymour and Thomas (1999)](https://annals.math.princeton.edu/1999/150-3/p05). The addition here is applying the fragment obstruction below to the published Folkman question.

### 3. Both Fano fragments are impossible for graph triangles

Label the Fano triples \(012,034,056,135,146,236,245\). Encode each of seven graph edges as its endpoint-indicator column over \(\mathbb F_2\). Each column has two ones, and the xor of the columns for a triangle is zero. The sum of the weights of all rows is 14.

- With a deleted line, choose it to be \(012\) (full Fano also implies this configuration). At every graph vertex, write the seven row bits as \(a,b,c,d,e,f,g\). The six surviving equations force \(c=a+b,e=a+d,f=b+d,g=c+d\). The row entries are therefore the seven distinct nonzero linear forms of \((a,b,c)\). Its weight is 0 or 4.
- With a deleted point, choose it to be 6. Retain graph-edge columns for \(0,1,2,3,4,5\), and use the actual external graph edge on the dangling line \(056\) as the seventh. The four intact equations together with \(056\) force \(c=a+b,e=a+d,f=b+d,g=a+b+d\). Again the entries are the seven nonzero linear forms in three free bits and the row weight is 0 or 4.

These statements use transitivity of the Fano plane on lines and on incident point/line flags. Both cases make the total a multiple of four, contradicting 14. The argument does not even require the external edge label to be distinct from every internal label.

### Replay

The dossier is standalone on Lean 4.34.1 and Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Use a built Mathlib with that pin and run
`MATHLIB_DIR=/absolute/path/to/mathlib LEAN_BIN=/absolute/path/to/lean bash replay.sh`.
The two graph declarations print their axiom dependencies. The finite row identities are verified with kernel `decide`, not `native_decide`.
