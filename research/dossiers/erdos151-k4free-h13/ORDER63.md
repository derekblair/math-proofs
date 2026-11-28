# The order-63 proof

The target is the K4-free case of Problem 1 in
[Erdős, Gallai and Tuza, *Covering the cliques of a graph with vertices*](https://doi.org/10.1016/0012-365X(92)90681-5).
In the edge-colorable case, an independent set in the red subgraph with lone
edges added meets no forbidden clique in full; this is covered by the
existing maximal-clique adapter. Otherwise take an inclusion-minimal
triangle-Ramsey edge core. The absence of a free 13-set bounds all ambient
degrees by 12. Every nonisolated core vertex has degree at least eight and
every core edge lies in at least two core triangles.

At a core vertex use the score “directed link degree sum minus three
times core degree”. The sum of the scores is nonnegative by the
formalized edge-critical triangle density theorem. The nine-neighbor
case is the only possible positive score.

* **Sender classification.** The complete Lean enumeration normalizes
  every dense triangle-free nine-link at a maximum-degree pivot. A
  numbered chart either supplies a priced three-hub deletion with a
  41-vertex pool remaining, or is isomorphic to chart 83 or 88. The
  kernel checks that all 76 right-block encodings give exactly the
  3,168 checked rows. In either exceptional chart density implies
  equality of ambient induced and core links. The source score is one.
  It sends its unit to the unique degree-four link position. The four
  common core neighbors have no added attachment through the source's
  ambient link, and no pair shares a vertex outside that link.
* **Strict capacity.** Each remaining neighbor of a receiving vertex
  is adjacent to at most one of the four source positions. A receiving
  nine-link has directed sum at most 24 and receives at most two units.
  Equality in the neutral ten-link would force an exterior K(2,3);
  its two degree-three exterior vertices give a safe three-hub
  insertion with two retained center vertices. The remaining
  ten-link deficits and the higher-degree slot bounds cover their
  actual unit loads with a strict surplus. Finite unit routing forces
  all scores to be zero.
* **Coloring.** The only possible nonisolated core links are the
  order-eight 12-edge named rows and cubic order-ten links. The
  low/high incidences exclude row 2 even in the mixed case, leaving
  the Wagner row at order eight. Every triangle-free cubic ten-link
  has three-edge cuts and remains connected after deleting two
  vertices. If it has no square, Moore equality gives the exact
  Petersen model. Components with a square use the verified actual
  triangle-edge incidence coloring; pure locally Petersen components
  use Hall's published recognition input and the checked KG(7,2)
  coloring, pulled back along the cover.

The new finite graph census, price transfer, receiver calculation,
Moore equality, component gluing, and color verification are all checked
in Lean. The order-63 theorem uses neither the published R(3,11) upper
bound nor an external ten-vertex chart catalogue.

## The same argument at larger orders, without R(3,11)≤50

The finite sender calculation, strict routing, and local mixed-core
proof apply uniformly at all orders at least 63. Use all three cases
of Hall's published recognition theorem, rather than the order-63
corollary. The third case is the published 65-vertex Doro–Hall graph.
The new exact color certificate covers all of its 325 triangles and
pulls back along the map in Hall's statement. Thus the uniform proof
uses R(3,10)≤41 and Hall's classification, but no R(3,11) bound.

## Covering every value of H(63)

The triangle-free 63-vertex circulant of
[Coniglio et al.](https://arxiv.org/abs/2608.18769) has independence
number 13. The authors' published witness uses the symmetric
difference set {3,4,9,15,17,25,38,46,48,54,59,60} modulo 63 in the
triangle-free color. Their [author-supplied file](https://github.com/fabiofurini/ramsey-number-lower-bounds/blob/main/docs/certificates/R_3_14_graphSize_63.clq)
lists the complement, blob 08774a21638ab00afa436e2701b420e7b16241a0.
The root-translation proof and the exact independent-set checker are
included between Core64.lean and Seed64Endpoint.lean. This upper
bound for H(63) and the earlier smaller-k proofs give the original
K4-free inequality for every possible H(63), not merely H(63)=13.
