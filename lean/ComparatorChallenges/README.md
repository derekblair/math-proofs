# [Comparator](https://github.com/leanprover/comparator) challenges

Install `comparator`, `landrun`, and `lean4export`, and make them available on `PATH`.
Then, from `lean/`:

```sh
lake update
lake exe cache get
lake env comparator ComparatorChallenges/ESIdentity.json
```

Each `.lean` file in this directory defines the problem statement standalone (from `Mathlib` only) and states the target theorem(s) with `sorry` **by design** — the challenge file states, and the corresponding module under `Mathproofs/` proves without `sorry`. The matching `.json` file configures `comparator` to verify statement identity and permitted axioms (`propext`, `Quot.sound`, `Classical.choice`).
