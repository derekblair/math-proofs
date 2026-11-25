# Open-problem results, 2026-11-25

Eight standalone Lean files address nine numbered literature questions or conjectures (counting each number once). The files are kept as a research dossier for review, separate from the default Lean build. The named theorems define the claims; no claim of absolute priority is made.

| Source and scope | Result | Lean file and principal theorem |
| --- | --- | --- |
| [Hussain, §6 Q1](https://arxiv.org/html/2611.27454v1#S6) | Logarithmic depth with explicit coefficient `k(k+2)` independent of homogeneity, plus an additive term. | [HussainQuestion1.lean](HussainQuestion1.lean), `HussainQ1.hussain_question1_real` |
| Hussain, §6 Q2 | Full C3 limit `r-1`, where `r` is the largest number of distinct ordered symbols admitting all equal blocks. | [HussainQuestion2Full.lean](HussainQuestion2Full.lean), `HussainQ2.hussain_question2_full` |
| Hussain, §6 Q4 | Counterexample: avoiding the subword 00 on binary length-three inputs gives deterministic depth 3 and nondeterministic depth 2. | [HussainQuestion4.lean](HussainQuestion4.lean), `HussainMembership.question4Counterexample` |
| Hussain, §6 Q5 | A linear `O(Nk)` classification algorithm for an explicit transition table, with a matching `(N-1)k` deterministic transition-probe lower bound in the corresponding model. | [HussainQuestion5.lean](HussainQuestion5.lean), `HussainQ5.question5_linear_upper` and `question5_matching_lower` |
| [Turau, §8](https://arxiv.org/pdf/2002.10752v4#page=12) | Counterexample to the proposed amnesiac flooding bound `k·Flood_k ≥ Rad + k − 1`: radius 10, four sources, three rounds, hence `12 < 13`. | [TurauFloodingCounterexample.lean](TurauFloodingCounterexample.lean), `TurauFlooding.turau_counterexample` |
| [Aires–Kahn, §12 Conj. 12.5(a,b)](https://arxiv.org/html/2509.11549v1#S12) | A 108-element poset violates both bounds: two chains of lengths 30 and 77, joined by `A_8 < x < B_25`. Deleting `x` retains `A_8 < B_25`. | [AiresKahnDeletion.lean](AiresKahnDeletion.lean), `AiresKahnDeletion.counterexample_12_5_a` and `counterexample_12_5_b` |
| Aires–Kahn, §12 Conj. 12.6(a,b) | The shift in mean rank is unbounded even when the directed chain length and the shortest cover-graph distance are both at least one eighth of the poset size. Part (c) is not addressed. | [AiresKahnLocalDeletion.lean](AiresKahnLocalDeletion.lean), `AiresKahnFamily.counterexamples_12_6_ab` |
| [Hussak–Trehan, Open Problem 2 and Theorem 4.3](https://link.springer.com/article/10.1007/s00446-023-00448-y) | The weighted square with three sources and a two-tick delay on one edge has a repeating nonempty state. An exactly-two-source bipartite witness is also provided. | [FixedDelayFlooding.lean](FixedDelayFlooding.lean), `FixedDelayFlooding.square_nontermination` and `exactly_two_sources_nontermination` |
| Hussak–Trehan, Open Problem 5 | Fixed-delay nontermination on a cylinder `C₄ × P₂` and a torus `C₃ × C₃`. The cylinder also covers the unrestricted acyclic second-factor class. | [FixedDelayFlooding.lean](FixedDelayFlooding.lean), `FixedDelayFlooding.cylinder_nontermination` and `torus_nontermination` |

### Scope

- Hussain Q3 is deliberately omitted. The upper bound for Q5 counts operations in the stated explicit-table model, not the wall-clock time of the Lean finite-set implementation.
- For Aires–Kahn 12.5, the certified lower bounds on the two left sides are about 107.032 and 1.025, above 107 and 107/109 respectively. They are lower bounds, not claims about the exact full sums.
- For 12.6(a,b), take two chains of length `4r−1`, insert `x` with `A_(2r) < x < B_(2r)`, and observe `B_(3r)`. Removing `x` reweights the shuffles by the number `K` of insertion gaps. Two finite reflection symmetries give the raw rank shift `1 + Var(K)/(4 E[K])`. For `r=2h²`, the verified bound is at least `1 + h/320`. The theorem gives an explicit directed cover walk and a matching lower bound for every undirected cover walk. It uses complete positional rank layouts, not sampled extensions.
- The fixed-delay model allows packets to pass without interacting in transit. On the square the complete pending state is the pair of opposite messages on edge 2–3 due next tick at both times 3 and 8 after the activation tick. The formalization also demonstrates nontransitivity of the relation in the paper's equation (19). It includes negative instances for classification Problems 3 and 4, but does not classify the graphs in those questions.
- Follow-up searches checked the exact statements, alternate wording and related literature. No earlier resolution surfaced for the results above in those searches. This is not a proof of priority, and no author endorsement or independent peer review is claimed.

### Reproduce the kernel checks

Use this repository's pinned Lean 4.34.1 and Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`. From `lean/`, with the Mathlib dependencies built:

```sh
for proof in ../research/dossiers/open-conjecture-results-2026-11-25/*.lean; do
  lake env lean "$proof" || exit 1
done
```

Each file prints the axiom dependencies of its exported certificates; the expected set is a subset of `propext`, `Classical.choice`, and `Quot.sound`. These research files are not imported into the default library or added to the published manuscript catalog in this PR.
