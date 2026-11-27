# Sharp Wu–Feng Lubell bound at excess five

For positive parameters (t,u) with (max(t,u)geq 2) and (n=t+u+5), the
maximum Lubell sum and an attaining original intersection–union family
are verified in Lean. This addresses this parameter range of
[Wu–Feng Problem 1.3](https://arxiv.org/html/2607.07564v1#S1), not the
whole weighted problem.

The final theorem `IU.Sharp5.sharp_five` covers either parameter order.
After reordering (tleq u), the exact score is that of the fixed
(t)-core family for (ugeq 2t-1), otherwise that of the block product.
The fixed core takes all extras of sizes 0, 1, 2 and the triples
containing one fixed extra point. In the block product, the first block
has (t+2) points and uses all subsets of size at least (t+1); the
second has (u+3) points and uses the empty set, all singletons and the
pairs containing one fixed extra point. The checked formula uses explicit
quotient masks and integer factored weights, and proves attainment.
It does not assert uniqueness.

Lean replays a completeness proof for the graph search, a 62-vertex
edge table, all 611 nodes of the checked clique tape (105 maximal
masks), and signed bivariate Newton coefficient inequalities for all
three parameter cones. The independent written comparison and
finite exact polynomial checks are described in the weighted
quotient dossier. All 236 Lean modules in this archive were replayed
from an empty output directory on Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The two final exact
optimum declarations use only `propext`, `Classical.choice` and
`Quot.sound`. There is no `native_decide` or `sorryAx` dependency
in either final statement.

The same replay includes the independent general theorem
`IU.UniversalCount.vertexCount_sum`: the exact quotient vertex count
equals a binomial sum over feasible deficits. The closed evaluation
described in COUNT.md has not been fully formalized in Lean.

## Replay

Verify the archive SHA-256:
`32ef0bad9f3a43f23d96dd793febc85eaf73395161b5a74504be88557132564b`.
Extract into an empty directory. Then, with built pinned Mathlib and the
pinned Lean binary, run:

```sh
MATHLIB_DIR=/absolute/path/to/mathlib LEAN_BIN=/absolute/path/to/lean bash replay.sh
```

The archive checks its source manifest and writes temporary proof
objects outside the sources. The exposed Lean files are identical to
the archived sources of the same names. Repository CI is separate.
This dossier makes no priority claim.
