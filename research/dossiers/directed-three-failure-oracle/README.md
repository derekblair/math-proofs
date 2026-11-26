# Exact directed three-failure distance oracle and batched shortcut proof

The [stopped-hierarchy oracle](STOPPED-ORACLE.md) handles three edge failures between fixed terminals in a simple directed graph with finite real weights and no negative cycles. Given a deterministic exact real APSP exponent 2 < α < 3, it has preprocessing O(n³ b^(α−3) log³(2+b) + n^α), persistent storage O(n³/b), and worst-case exact queries in O(b²). Here b is any block size from 1 to n. The bound on persistent storage does not count the temporary APSP engine. For b = √n, query time is O(n), persistent storage O(n^2.5), and preprocessing is truly subcubic.

The [full-depth proof](REPORT.md) derives deterministic O(n³) preprocessing plus O(n³) explicit adaptive failure reporting. Harada–Terao [§4](https://arxiv.org/html/2611.29061v1#S4) already announced both the O(n³) reporting endpoint and the high-level idea of batching shortcut removals in APSP. This is an independently written proof of that endpoint and a stopped-depth tradeoff, not a claim of priority or of beating their announcement. The address model uses unit-cost O(log n)-bit words; arbitrary real cells support exact addition, subtraction, and comparisons. The records are not all ordered triples of original edges.

Lean checks the [bit isolation lemma](TagIsolation.lean), not the full reduction, oracle implementation, imported APSP runtime, or memory theorem. The Python tests check small exact instances and use Floyd–Warshall as their APSP stand-in. They are not asymptotic benchmarks.

The [mixed-anchor extension](mixed-anchors/README.md) gives constant-time queries with subcubic preprocessing when the failed edges are covered by the fixed terminals and two further vertices. It also gives a parameterized bound for arbitrary triples on graphs with small support vertex cover. These are restricted-family bounds, not a faster unrestricted three-fault algorithm.

With Lean 4.34.1 and compiled Mathlib at commit `d13f23b723b8a846827a245b89c10fc7d3f11612`, run:

```sh
LEAN_BIN=/path/to/lean MATHLIB_DIR=/path/to/mathlib4 bash replay.sh
```
