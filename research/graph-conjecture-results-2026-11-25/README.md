# Lean-checked results on graph conjectures, 25 November 2026

This research drop settles 20 published conjectures: 18 counterexamples and 1 proof from
machine-generated conjecture lists, plus 1 counterexample to a conjecture stated by human authors
in a 2025 arXiv paper. Each row links to the Lean entry point. The bundles share the repository's
Lean and Mathlib pins. They do not change the default Lake targets or the formalization catalogue.

All proofs are kernel-checked. Finite facts about the witness graphs are checked with
`decide +kernel` (no `native_decide`). Every listed theorem depends only on
`propext`, `Classical.choice` and `Quot.sound`. No file contains `sorry`.

| Result | Exact Lean entry point |
| --- | --- |
| Boriboon–Kittipassorn Conjecture 4 ([arXiv:2508.17569](https://arxiv.org/abs/2508.17569)), counterexample; `m(7,3) = 14` and `m(7,4) = 11` | [Arxiv2508_17569.conjecture_4, .seven_three, .seven_four](boriboon-kittipassorn-conj4/BK73Answer.lean) |
| *Automated Conjecturing III* §3.2 even-hole-free sufficient condition, counterexample | [AC3EHF.not_conjecture](ac3-even-hole-free/AC3_EHF.lean) |
| Graffiti.pc (WOWII) #382c, counterexample | [WOWII382c.not_conjecture382c](wowii/WOWII382c.lean) |
| Graffiti.pc (WOWII) #392c, counterexample | [WOWII392c.not_conjecture392c](wowii/WOWII392c.lean) |
| Graffiti.pc (WOWII) #393d, counterexample | [WOWII393d.not_conjecture393d](wowii/WOWII393d.lean) |
| Graffiti.pc (WOWII) #394, counterexample | [WOWII394.not_conjecture394](wowii/WOWII394.lean) |
| Graffiti.pc (WOWII) #395a, counterexample | [WOWII395a.not_conjecture395a](wowii/WOWII395a.lean) |
| Graph Brain Project issue #421, lower bounds #15 and #18, counterexamples | [GBP421_015_018.not_conjecture15, .not_conjecture18](graph-brain-421/GBP421_015_018.lean) |
| Graph Brain Project issue #421, lower bound #19, proof (strengthened) | [GBP421_019.conjecture19_strong](graph-brain-421/GBP421_019.lean) |
| Graph Brain Project issue #421, lower bound #29, counterexample | [GBP421_029.not_conjecture29](graph-brain-421/GBP421_029.lean) |
| Graph Brain Project issue #421, lower bound #35, counterexample | [GBP421_035.not_conjecture35](graph-brain-421/GBP421_035.lean) |
| Graph Brain Project issue #421, lower bound #45, counterexample | [GBP421_045.not_conjecture45](graph-brain-421/GBP421_045.lean) |
| Graph Brain Project issue #421, lower bound #47, counterexample | [GBP421_047.not_conjecture47](graph-brain-421/GBP421_047.lean) |
| Graph Brain Project issue #421, lower bound #62, counterexample | [GBP421_062.not_conjecture62](graph-brain-421/GBP421_062.lean) |
| Graph Brain Project issue #421, lower bound #64, counterexample | [GBP421_064.not_conjecture64](graph-brain-421/GBP421_064.lean) |
| Graph Brain Project issue #421, lower bound #70, counterexample | [GBP421_070.not_conjecture70](graph-brain-421/GBP421_070.lean) |
| Graph Brain Project issue #421, lower bound #80, counterexample | [GBP421_080.not_conjecture80](graph-brain-421/GBP421_080.lean) |
| Graph Brain Project issue #421, lower bound #84, counterexample | [GBP421_084.not_conjecture84](graph-brain-421/GBP421_084.lean) |
| Graph Brain Project issue #421, lower bound #85, counterexample | [GBP421_085.not_conjecture85](graph-brain-421/GBP421_085.lean) |

Each Lean file opens with a docstring that quotes the source statement, gives the definitions
used, and describes the witness. See the [priority audit](PRIORITY.md) for related work and the
limits of the precedence claims.

## Scope notes

- **Boriboon–Kittipassorn.** S. Boriboon and T. Kittipassorn, *A Size Condition for Small
  Diameter Orientable Graphs*, arXiv:2508.17569v1. For `2 ≤ d ≤ n − 2`, `m(n,d)` is the least `M`
  such that every bridgeless graph of order `n` and size at least `M` has an orientation of
  diameter at most `d`. Conjecture 4 states `m(n,d) = C(n−d,2) + n + 2`. The paper proves it for
  `d = 2` (citing Cochran–Czabarka–Dankelmann–Székely) and `d = n − 2`, and proves the lower bound
  for `5 ≤ d ≤ n − 2`. We prove `m(7,3) = 14` (predicted 15) and `m(7,4) = 11` (predicted 12).
  So for `n = 7` and `d ∈ {3, 4}` the graph asked for in the paper's Problem 7 does not exist.
  - The upper bounds are computer-assisted. A verified checker (`BK73Core`, `BK73Core4`, with
    soundness lemmas in `BK73Sound1`) is run by `decide +kernel` over all graphs on `Fin 7` with
    at least 14 edges (for `d = 3`) or at least 11 edges (for `d = 4`). Only edge sets with sorted
    degrees are enumerated (the reduction is proved), and for each one an orientation from a fixed
    candidate list is checked. The search is split into chunk modules (`BK73Chunks0`–`7`, 968
    theorems, for `d = 3`; `BK73C4_00`–`63` for `d = 4`), which `BK73Assemble*` combines.
  - The lower bounds are explicit bridgeless graphs with no orientation of the required diameter:
    `FCZnw` (13 edges, `d = 3`) and `F?qvo` (10 edges, `d = 4`) in graph6 notation
    (`BK73LB*`, `BK73FinalEq`, `BK73Final4`).
  - `BK73Statement.lean` states the problem with the same definitions as the companion
    formal-conjectures statement file, and `BK73Answer.lean` proves it from the computation.
  - Building this bundle is expensive: about 1.6 CPU-hours to compile, with up to about 4 GB
    of RAM per chunk module. Kernel replay with `leanchecker` roughly doubles that.
- **GBP #19** is proved in a stronger form: `⌈|S| / sw(G)⌉ ≤ α(G)` for every vertex set `S` of
  every finite graph, by the greedy Szekeres–Wilf bound `n ≤ sw(G)·α(G)`. This is elementary. It
  covers #19 whatever the exact irreducible part is, since that part is some vertex set.
- **GBP #80** is stated for graphs with a cycle, because Sage gives trees girth `+∞`. **GBP #45**
  is stated for graphs with a non-adjacent pair, so that `σ₂` is defined.
- The GBP, WOWII and AC3 conjectures come from computer conjecturing programs (Graffiti.pc and
  the Larson–Van Cleemput conjecturing program). Their counterexamples have modest mathematical
  weight. They are listed because the lists mark them as open.

## Reproduce Lean verification

Use Lean 4.34.1 and the built Mathlib checkout at revision
`d13f23b723b8a846827a245b89c10fc7d3f11612` (the revision pinned under the repository's `lean/`
directory).

```sh
python3 research/graph-conjecture-results-2026-11-25/verify.py /path/to/mathlib4 wowii graph-brain-421 ac3-even-hole-free
# The Boriboon–Kittipassorn bundle takes several hours with this sequential verifier:
python3 research/graph-conjecture-results-2026-11-25/verify.py /path/to/mathlib4 boriboon-kittipassorn-conj4
```

The verifier is the one from `research/lean-verified-2026-11-25/`, with no negative controls. It
rebuilds each bundle in a fresh temporary directory in dependency order, checks the axiom reports,
and replays each compiled module with `leanchecker`.
