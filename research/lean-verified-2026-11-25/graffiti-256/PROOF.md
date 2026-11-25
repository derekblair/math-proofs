# A 15-vertex counterexample to Graffiti.pc Conjecture 256

**Source:** Ermelinda DeLaViña, *Written on the Wall II*, conjecture 256, announced February 23, 2007. The November 5, 2026 edition still labels it open (printed pp. 148–149). [Official catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf).

For a finite simple connected graph, let A be the vertices of minimum degree, N(A) the union of their open neighborhoods, and M the largest number of vertices adjacent to at least one endpoint of an edge. The conjecture says the total domination number is at least 2|N(A)|/M. Catalogue items 121 and 259 define N(A) as that union and explicitly subtract A where intended. Item 256 does not subtract A.

## Witness

Start with a three-vertex path x–b–y. Join six new vertices to x and a separate six to y. Add three disjoint edges joining pairs among the six on each side. There are no other edges.

- The graph is simple and connected. The hubs x and y have degree 7. The other 13 vertices have degree 2. Each of the 12 wing vertices has a degree-2 partner, and both hubs are adjacent to b. The middle vertex b is adjacent only to the hubs, so N(A) is all 15 vertices except b.
- At either path edge, the union of the endpoint neighborhoods has size 9. At a hub-to-wing edge the union has size 8. At a wing-pair edge it has size 3. Thus M = 9.
- The three path vertices form a total dominating set. A total dominating pair would have to be adjacent in order to dominate itself, but its combined neighborhood would then have at most 9 vertices, not 15. A singleton cannot totally dominate itself in a loopless graph. Therefore the total domination number is 3.

The conjectured inequality would require 3 ≥ 28/9. In integer form, 27 < 28 disproves it.

## Verification and prior work

`WowII256.lean` uses only Lean's standard library. It checks the values on the explicit adjacency relation, proves graph connectivity through actual walks, and proves the negation of the universal cross-multiplied inequality. This is equivalent to using the minimum total dominating set size on finite graphs of order at least two: the inequality holds for the minimum exactly when it holds for every total dominating set. The certificate needs only the upper bound from the displayed set and also checks that no pair suffices. The Lean kernel checked `WowII256.refutesConjecture` with only the standard axioms `propext` and `Quot.sound`; no `sorry` or native oracle. Two deliberately wrong certificates were rejected. Run `bash check.sh` with Lean 4.34.1 on PATH, or provide `LEAN_BIN`. The Python verifier is separate and not a Lean proof dependency.

The two-hub path was inspired by the catalogue's known counterexample to **different** conjecture 257, which attaches unmatched leaves. The added matching and the resulting degree-2 neighborhoods address 256. I found no earlier resolution of this exact statement in targeted catalogue, preprint, repository, or published worklog searches as of November 25, 2026. This is not proof of absolute priority. No minimality is claimed.
