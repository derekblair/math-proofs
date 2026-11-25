# Lean-verified literature results, 25 November 2026

This research drop contains 15 distinct conjectures or posed open questions. Each row links to the controlling formal statement. Stronger bounds or counterexamples for a single question are counted once. These independent proof bundles share the repository's Lean and Mathlib pins but do not change the default Lake targets or the formalization catalogue.

| Result | Exact Lean entry point |
| --- | --- |
| Graffiti.pc #255, counterexample | [WowII255.refutesConjecture](graffiti-255/WowII255.lean) |
| Graffiti.pc #256, counterexample | [WowII256.refutesConjecture](graffiti-256/WowII256.lean) |
| Graffiti.pc #268, proof | [Wow268.conjecture268](graffiti-268/Result.lean) |
| Graffiti.pc #269, counterexample | [Refute269.not_graffiti269](graffiti-269/Answer269.lean) |
| Graffiti.pc #271, proof | [Wow271.conjecture271](graffiti-271/Answer271.lean) |
| Hassler–Kirgizov Conjecture 5.1, counterexample | [Emerging.refutesPublished](hassler-kirgizov-zero-popularity/Statement.lean) |
| Hassler–Kirgizov §5 question 3, irrational limiting popularity | [FibPopularity.question3](hassler-kirgizov-irrational/IrrFinal.lean) |
| Hassler–Kirgizov §5 question 4, nonconvergence | [Nonconv.question4](hassler-kirgizov-nonconvergence/NonconvFinal.lean) |
| Demonstrandum §7, exact cubic-chain domination and zero forcing | [ZFChain.publishedChainConjecture](cubic-zero-forcing-chain/ExactChain.lean) |
| Bevan–Homberger–Tenner Q5.5, nondegenerate permuted-circle limit | [PermCircles.question55_paper](permuted-circle-packing/LiteralPaper.lean) |
| Bevan–Homberger–Tenner follow-up for regular hexagons, any fixed orientation | [PermHex.regular_hexagon_limit](permuted-hexagon-packing/LiteralHex.lean) |
| Blitvić–Kammoun–Steingrímsson §7 item 5, the stated overlap-two separator conjecture | [PackingSeparator.bks_section7_item5](bks-separator/SourceForm.lean) |
| Blitvić–Kammoun–Steingrímsson §7 item 6, the uniform Catalan part | [FussCover.uniform_catalan_pattern](bks-uniform-catalan/CatalanAnswer.lean) |
| Blitvić–Kammoun–Steingrímsson §7 item 8, no uniform bound independent of pattern length | [CoverCutoff.no_uniform_cutoff](bks-packing-cutoff/ArbitraryCutoff.lean) |
| Haugland–Omland §4(iii), no binary degree-two proper lifting | [QuadraticCA.no_degree_two_proper_lifting](quadratic-cellular-automata/QuadraticAnswer.lean) |

The separator result is not a general classification. The Catalan result does not claim Nagy's double-factorial result or a general Fuss–Catalan formula. The cutoff result does not rule out a bound depending on pattern length. The geometric entries distinguish positive-area boards from the degenerate singleton. The cubic-chain entry concerns the later exact chain formulas, not the earlier conjecture refuted by that construction's authors. See the [priority audit](PRIORITY.md) for related work and limits on claims of precedence.

## Reproduce Lean verification

Use Lean 4.34.1 and the built Mathlib checkout at revision `d13f23b723b8a846827a245b89c10fc7d3f11612` (the revision pinned under the repository's `lean/` directory). If Mathlib modules are missing, run `lake exe cache get` in the `lean/` project before verification.

```sh
python3 research/lean-verified-2026-11-25/verify.py lean/.lake/packages/mathlib
# Or verify a single bundle:
python3 research/lean-verified-2026-11-25/verify.py lean/.lake/packages/mathlib bks-separator
```

The verifier uses a fresh temporary directory for each bundle, rebuilds its modules in dependency order, and replays each compiled module with Lean's kernel checker. The Python controls are supplementary and not proof dependencies.
