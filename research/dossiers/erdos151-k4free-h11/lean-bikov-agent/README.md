# Bikov's seven-vertex marked-link exclusion

Primary source: Aleksandar Bikov, Small minimal (3,3)-Ramsey graphs,
https://arxiv.org/pdf/1604.03716, Proposition 3.4 and Theorem 8.2.
This re-verifies the published minimum-degree bound, not the degree-eight
classification or a new general result.

Every triangle-free graph on at most seven vertices has a bipartition
with at most one internal edge. For any edge coloring of a link, color
the new spokes by the two sides. All crossing edges are safe. On the
sole possible noncrossing edge the two spokes can be made opposite
to that edge by flipping all spoke colors if necessary.

A bipartite graph is immediate. Otherwise choose a shortest odd cycle:
it has length five or seven, and is chordless since a chord splits it
into two shorter cycles of opposite parity. The usual parity-from-a-root
argument gives an odd closed walk if no bipartition exists, and splitting
at a repeat gives a simple odd cycle. If the cycle has length seven it
accounts for the whole graph, and alternating colors have one defect.
Otherwise label the induced 5-cycle 0,1,2,3,4 cyclically and pad to
seven vertices 0..6 with isolates. It suffices to handle maximal
triangle-free extensions; a cut with ≤1 internal edge restricts.

The outside vertices 5,6 each have an independent cycle neighborhood
of size at most two. In a maximal extension both reach size two.
If they are nonadjacent one can enlarge an empty or singleton
neighborhood independently. If they are adjacent the neighborhoods
must be disjoint; an empty neighborhood is still enlargeable, and
a singleton {i} has two possible independent enlargements i±2.
Those two points are adjacent on C5, so the other independent
neighborhood cannot block both. The outside vertices are adjacent
precisely when their neighborhoods are disjoint, by maximality.

There are three types up to dihedral relabeling and swapping 5,6:

| N(5) in C5 | N(6) in C5 | edge 5–6 | one side of cut |
|---|---|---|---|
| {0,2} | {0,2} | no | {0,2} |
| {0,3} | {0,2} | no | {0,2,3} |
| {1,3} | {0,2} | yes | {0,2,5} |

For the intersecting case fix the common point 0; the possible partners
are 2 and 3. For the disjoint case fix {1,3}; the two allowable pairs
in {0,2,4} are {0,2} and {2,4}, interchanged by reflection. The cuts
displayed above directly have one internal edge.

For a K4-free minimal (3,3) edge-Ramsey graph, deleting a vertex v
leaves a red/blue edge coloring without monochromatic triangles.
Its link is triangle-free, since any triangle there would span a K4
with v. If its size were at most seven, the local extension would
color the original graph without monochromatic triangles, a contradiction.

## Lean verification

The declaration BikovLocal.bikov_degree_eight (MinimumEight.lean) proves
the minimum-degree bound on an arbitrary symmetric irreflexive relation
with finite neighbor subtype, the local no-K4 condition, Ramsey, and
a symmetric coloring of the vertex deletion. The only printed axioms
are propext, Classical.choice, and Quot.sound.

LinkCuts, LinkCoverage, and LinkSound use 25 labelled cut certificates
and test all 2048 candidate bit masks via kernel reduction.
LinkEncoded interprets arbitrary adjacency and edge labels.
ShortOdd constructs a bipartition if there is no odd closed walk and
otherwise identifies an injective chordless shortest odd walk.
LabelCycle proves the length-five/seven characterization and permutation
relabeling. MinimumEight assembles all cases, pads a smaller finite
link with isolates, and applies the ambient symmetric lift (LinkLift).
local_enum.py is an independent exact control, not a trusted Lean dependency.

Replay with Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
Run bash replay.sh for all source modules (check SHA256SUMS first); set
BIKOV_TOOLCHAIN to the directory containing lean-4.34.1-linux and mathlib4
if copying the dossier outside its original layout.

CoreExtract.lean derives an edge-minimal Ramsey core from any finite
input graph in this scope. It retains an edge, has degree at least eight
at each nonisolated vertex, and has two distinct common neighbors on
every core edge. The last assertion follows by extending a coloring of
an edge deletion whenever there is at most one triangle on that edge.
