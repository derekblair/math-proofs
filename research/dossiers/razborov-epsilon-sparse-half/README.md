# Razborov's epsilon question for sparse halves

This dossier presents an independently audited **paper proof candidate** for Razborov's explicit intermediate question: is there an absolute ε > 0 such that a triangle-free graph with independence ratio at least 2/5 − ε has a sparse half? It does not claim the unrestricted Erdős #128, an explicit ε, or a priority result.

Start with [RAZBOROV-EPSILON.md](RAZBOROV-EPSILON.md). The new step forces any putative limiting obstruction to have no vertices with A-degree below 1/5; it either constructs a weighted Case 2 certificate or takes the larger side of every complementary pair and fills from the low set. The other two notes detail saturation/rigidity and why the maximum-independent-set cap transfers to active sides without assuming upper semicontinuity of independence.

**Lean scope:** the 22 standalone modules check scalar bounds, finite weighted support/averaging steps, and the endpoint arithmetic. The colored compactness, graphon decomposition and integrations, endpoint classification as a complete graph theorem, odd rounding, and transfer to Norin–Yepremyan's established local results are paper-only. There is no end-to-end Lean theorem for the intermediate question yet; keep this draft open.

Run replay.sh with MATHLIB_LEAN_PATH set to the colon-separated Lean library paths and LEAN_BIN set to the Lean executable. Pinned inputs are Lean 4.34.1 (5045d0056413266e57c625dcd7c365b10e377c52) and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 plus its pinned dependencies. The replay builds in a fresh temporary directory.
