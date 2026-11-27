# Directed k-disjoint shortest paths: smaller exponent

[Strongest bound and proof](BALANCED.md). The full positive-real directed problem has a deterministic exponent bound O(k^5·4^k) using the published sweep; the earlier [factorial bound](PROOF.md) explains the common nesting and width transfer. The proof counts the recursion actually taken by its width analysis, not every separated packing. The paper's polynomial-in-k exponent question remains open. This is a draft research handoff, not a priority claim.

## Lean companion

`DirectedAnchorCounting.lean` kernel-checks the signed-fiber argument and the weighted bound on the length of a branch, with the suffix-separation, chosen cheap-cycle and aligned non-repetition premises stated explicitly. It does not formalize Cao–Qi–Wang's geometry, the no-repetition lemma itself, the cycle-label count, or the sweep algorithm and its running time. The full result is a paper proof using those sources.

`DirectedAnchorPreimage.lean` separately checks the permutation-prefix pigeonhole lemma and chronological interval composition used in the stronger bound. It does not formalize the routing compression or recurrence.

Set `LEAN_BIN` to Lean 4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52). Set `MATHLIB_LEAN_PATH` to the library paths for Mathlib commit d13f23b723b8a846827a245b89c10fc7d3f11612 and all its packages. Run `bash replay.sh` for a fresh compilation and axiom report. The reported declarations use only propext, Classical.choice, and Quot.sound.
