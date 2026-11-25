# A 268-vertex counterexample to Graffiti.pc Conjecture 269

[Ermelinda DeLaViña, *Written on the Wall II*, Conjecture 269, p. 156](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf#page=156) states that a simple connected C₄-free graph has total domination number at least the ceiling of one plus the mean distance between distinct center vertices. The November catalogue still labels the problem open. The sources searched did not reveal a prior item-specific resolution; we do not claim exhaustive bibliographic priority. The graph below has every vertex in its center, so the counterexample also works if the mean is read as center-to-all rather than center-to-center.

## The graph

* Start with four vertices numbered 0, 1, 2, 3 and the two edges 0–1 and 2–3.
* Add 35 internally disjoint paths 0–x–y–3 of length three. On each path, add one vertex adjacent just to 0 and x, and a second adjacent just to 3 and y.
* Add 62 internally disjoint paths 1–u–v–2 of length three. No other edges.

This gives 268 vertices and 433 edges. There is no four-cycle, even counting cycles with chords. The radius is four and every vertex is a center. The four initial vertices are a minimum total dominating set. The 71,556 ordered distinct pairs have sum of distances 214,680, so the mean is exactly 17,890/5,963. It exceeds three by 1/5,963. The conjecture demands five; the actual total domination number is four. No global minimality claim is made.

## Verification

The formal statement is `Refute269.Conjecture269` and its negation is `Refute269.not_graffiti269` in `Answer269.lean`. Set the Lean 4.34.1 bin directory on PATH, give `verify269.sh` the path to an already built Mathlib v4.34.1 tree at commit `d13f23b723b8a846827a245b89c10fc7d3f11612`, and run:

```sh
./verify269.sh /path/to/mathlib4
```

Exactly checked shortest paths on the 16-vertex graph with two tracks of each kind transfer to every pair of vertices using two adjacency-preserving reindexings. For the no-four-cycle certificate, potentially offending quadruples map injectively on their four vertices to a graph with four tracks of each kind. Sums are computed by role, with correct same-track and other-track multiplicities. The proof of exact total domination number uses the companion floor inequality; the four explicit dominators alone suffice to refute the ceiling inequality. The companion proof uses the spanning-tree approach of [DeLaViña et al. (2007)](https://www.uhd.edu/documents/academics/sciences/total-dom-2007.pdf).

`python Verify269.py` separately computes distances on the full graph using the Floyd–Warshall algorithm and exact rational arithmetic.
