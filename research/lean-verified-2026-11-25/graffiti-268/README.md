# Graffiti.pc Conjecture 268, proved in Lean

[Ermelinda DeLaViña's *Written on the Wall II*, November 5, 2026](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf), printed pp. 155–156, lists conjecture 268 as open: for a finite simple connected graph, the total domination number is at least `floor(1 + dist_avg(C))`, where `C` is the center. The definition of `dist_avg(C)` is on pp. 88–89 and p. 142: average only the positive shortest-path distances between two center vertices. Including ordered rather than unordered pairs does not change the mean. Empty pair sets (a singleton center) have average zero in this implementation. The graph has at least two vertices so that total domination is defined. The theorem quantified over all total dominating sets is also present, with no explicit nontriviality assumption.

The exact theorem is `Wow268.conjecture268` in `Result.lean`. It uses the minimum cardinality of a total dominating set. The proof establishes the slightly stronger transparent inequality `avg(C) < |S|` on the way to the floor inequality for every such set `S`. It does not prove the separate ceiling conjecture #269.

## Proof idea

Start with any total dominating set of size `s`. Keep it while removing one edge at a time from cycles until a spanning tree remains. If a cycle contains a vertex outside the set, one of the two cycle edges at that vertex can be removed without destroying total domination. If the cycle is entirely inside the set, either cycle edge at any vertex can be removed.

In the spanning tree, retain all chosen vertices and all vertices of degree at least two. This connected core still dominates the original tree and has at most `2s−2` vertices. To see the count, choose one incoming dart for every vertex from a chosen neighbor. Those darts all start in `S` and are distinct. The sum of degrees outside `S` is therefore at most `n−2`; since each outside vertex contributes at least one, at most `s−2` of them can have degree at least two.

In a tree on at most `2k` vertices, two adjacent vertices can both have eccentricity at most `k`. Minimize the sum of distances. At the minimizer, every branch has at most half the vertices; place the second vertex in a branch of size exactly `k` if one exists, and otherwise take any neighbor. Apply this to the core with `k=s−1`. The original graph thus has two adjacent vertices of eccentricity at most `s`. If its radius is strictly smaller, every center-pair distance is smaller than `s`. If its radius equals `s`, the adjacent vertices are both centers, and their distance is `1<s`; all other center-pair distances are at most `s`. In either case the mean is strictly smaller than `s`.

The older [DeLaViña–Liu–Pepper–Waller–West paper](https://www.uhd.edu/documents/academics/sciences/total-dom-2007.pdf), Theorem 3 and Lemmas 2–3, proves the radius bound using a spanning tree. The proof here retains the adjacent-center conclusion at equality, which is what settles the catalogue's floor-average statement. Literature and repository searches by catalogue number, exact invariant, and formal theorem name did not surface an earlier settlement of this exact conjecture. That is a bounded priority check, not an exhaustive claim.

## Reproduce

Use Lean 4.34.1 and Mathlib v4.34.1 at commit `d13f23b723b8a846827a245b89c10fc7d3f11612`. In the Mathlib checkout, fetch or build the following modules:

    lake build Mathlib.Combinatorics.SimpleGraph.Diam Mathlib.Combinatorics.SimpleGraph.Acyclic Mathlib.Data.Rat.Floor Mathlib.Tactic

Then run:

    /path/to/unpacked/verify.sh /path/to/mathlib4 /path/to/output-logs

This compiles every bundled theorem module in a clean temporary directory, checks the axiom reports, and replays all bundled module declarations using `leanchecker` against their imports. This is kernel replay, not a separate external checker or a fresh replay of all of Mathlib. Axiom and replay logs are included. `Controls.lean` verifies the exact average on the two-vertex graph and refutes the false variant obtained by putting 2 in place of 1 inside the floor. `test_small.py` independently checks all labelled connected simple graphs on 2 to 6 vertices; that Python test is not a dependency of the proof.
