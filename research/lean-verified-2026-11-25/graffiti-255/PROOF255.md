# An 11-vertex counterexample to Graffiti.pc Conjecture 255

[Ermelinda DeLaViña, Written on the Wall II](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf), printed p. 148. The November 5, 2026 version lists conjecture 255 as open. It asserts that the total domination number of a simple connected graph is at least twice the size of its center divided by the largest open neighborhood of an edge. An edge's open neighborhood is the union of its two endpoints' open neighborhoods. In particular that union includes the endpoints themselves.

Take a path x–b–y. Attach a four-vertex clique L to x (join each clique vertex to x) and four independent vertices R to y. Add a perfect matching between L and R. There are 11 vertices and 20 edges.

* Every vertex has eccentricity exactly two. There is no universal vertex. Two vertices in either wing are joined by a walk via their hub; a left vertex can reach a right vertex in at most two steps via that right vertex's match. The middle vertex reaches each wing via its hub; a hub reaches the opposite wing via the matching; the hubs are distance two apart. Thus the center is the entire graph.
* The maximum edge-neighborhood size is 7. Each path edge, each x–L edge, each edge inside L, and each matching edge attains 7. A y–R edge has union size 7 as well: the four R vertices and b are adjacent to y, and y and the left match are adjacent to the R endpoint. These exhaust the edge types.
* The three path vertices form a total dominating set. No singleton can dominate itself, and any total dominating pair would have to be adjacent but an edge's neighborhood contains at most 7 of the 11 vertices. The total domination number is 3.

The conjecture would require 3 ≥ 22/7, contradicted by 21 < 22.

## Lean and novelty

`WowII255.refutesConjecture` is the Lean-checked negation of the cross-multiplied inequality, stated for every distinct total dominating set. In a finite connected graph this is equivalent to the inequality on the smallest such set. The graph's center is characterized by the distance-threshold order: a center reaches every vertex by any distance bound that holds at any other vertex. The proof derives actual bounded walks, connectivity, and the center characterization. The numeric cert uses kernel reduction, not native evaluation or a supplied external axiom. Run `bash check255.sh` with Lean 4.34.1 on PATH and Python 3, or pass `LEAN_BIN`. The script independently enumerates the witness in Python and requires Lean to reject two mutated certificates.

The source catalogue lists #255 open; targeted exact-identifier and invariant-language searches across preprints, indexed repositories, and known related public worklogs found no prior resolution, as of November 25, 2026. Henning and Yeo's similarly titled 2014 paper (doi:10.1016/j.dam.2014.03.013) proves #233, not #255. A bounded search cannot certify absolute priority. No claim of minimum order is made.
