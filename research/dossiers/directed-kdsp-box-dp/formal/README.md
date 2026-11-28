# Verified components of the box dynamic program

| File | Checked statement |
| --- | --- |
| BoxClip, ClipProgress | Closed interval or empty after finite clipping; own coordinate progress remains monotone and ordered across clipped segments. |
| BoxCore, BoxAverage | Finite weighted averaging and double count for an at-most-9k cut from the per-arc projection budgets. |
| BoxExit, BoxBudget | Affine face exit and exact inherited ancestor face charging with the ancestor budget. |
| BoxShrink, FiniteScale, ShrinkHorizon | Longest-side block contraction, finite positive gaps, and one geometric-depth bound for all histories. |
| RankCuts | Real cut induces the exact two rank children, without computing the real threshold. |
| BoxRoster, RosterTree | Per-vertex exact labeled incidence gluing, and soundness/completeness over a fixed tree with bounded witness boundaries. |
| BoxToken, FlowPaths | Earliest-token invariant, finite scheduling, and no disconnected components in a strictly increasing selected arc roster. |

The assembled result in ../BOX-DP.md is a paper proof. In particular, these
modules do not assemble a full geometry instance into a recursively
constructed split tree, encode the finite rank-box search as executable Lean
code, or verify its running time.

To replay: point `LEAN` at Lean 4.34.1 and `MATHLIB` at a built Mathlib
v4.34.1 checkout (d13f23b723b8a846827a245b89c10fc7d3f11612).
From a scratch copy of this directory, run `bash replay.sh`.
