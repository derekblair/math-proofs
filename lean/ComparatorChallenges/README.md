# [Comparator](https://github.com/leanprover/comparator) challenges

Install `comparator`, `landrun`, and `lean4export`, and make them available on `PATH`.
Then, from `lean/`:

```sh
lake update
lake exe cache get
lake env comparator ComparatorChallenges/ESIdentity.json
```

Each `.lean` file in this directory defines the problem statement standalone (from `Mathlib` only) and states the target theorem(s) with `sorry` **by design** — the challenge file states, and the corresponding module under `Mathproofs/` proves without `sorry`. The matching `.json` file configures `comparator` to verify statement identity and permitted axioms (`propext`, `Quot.sound`, `Classical.choice`).

## Provenance and inventory

The 17 challenge pairs (`.lean` + `.json`) in this directory did not exist prior to the November 2026 repository restructure (`b2e4a11`); they were newly authored in PR #45 (`b2f02d4`) by extracting standalone definitions and theorem signatures from `Mathproofs/`. Together they contain **39** deliberate `sorry` placeholders: the 38 flagship theorems listed under `status.main_results` in [`../formalization.yaml`](../formalization.yaml) plus the helper theorem `Girth5Floor3v.scores_nonempty` in [`Girth5Extremal.lean`](Girth5Extremal.lean#L73-L75) (listed in [`Girth5Extremal.json`](Girth5Extremal.json)).

`ComparatorChallenges` is declared as a non-default Lake library (`lean_lib ComparatorChallenges` in [`../lakefile.lean`](../lakefile.lean)) and is excluded from `@[default_target]` and from `Mathproofs.lean`: default `lake build` compiles `0` `ComparatorChallenges` modules and emits `0` `sorry` warnings. Dual-environment Lean 4 kernel `Expr` comparison verified exact statement and definition-body identity across all 17/17 pairs; running official `leanprover/comparator` on Lean 4.34.1 remains pending compatible `comparator`/`lean4export` toolchain binaries.
