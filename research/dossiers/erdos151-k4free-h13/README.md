# Erdős #151: K4-free at order 63, and H(n)=13 at order at least 63

The [order-63 Lean theorem](N63FullOrder.lean) establishes the full
K4-free inequality at that order, without needing to know H(63) exactly.
It covers all triangle-free guarantees k at order 63.
The [published 63-vertex circulant](https://arxiv.org/abs/2608.18769)
from Coniglio et al. rules out k≥14, and its triangle-free status and
independence number are replayed in Lean. This is a verification of
the authors' existing Ramsey witness, not a new lower bound.

The principal [Lean theorem](H13AtLeast63Hall.lean) proves that an n-vertex K4-free
graph with n≥63 and H(n)≥13 has a transversal of at most n−13 vertices
meeting every inclusion-maximal nontrivial clique. H(n) is the independent-set
size guaranteed for all triangle-free graphs on n vertices. For H(n)>13,
this statement does not give n−H(n). It does not prove the unrestricted
conjecture. Orders below 63 are not covered by this H(n)=13 theorem.

The principal theorem takes two published inputs:
[Angeltveit's R(3,10)≤41](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v32i4p30)
and [Hall's locally Petersen classification](https://doi.org/10.1002/jgt.3190040206).
The 21-vertex KG(7,2) and its 63-vertex triple cover share one checked
edge coloring via pullback; [Cohen, pp. 87–89](https://ir.cwi.nl/pub/2362/2362D.pdf)
gives the cover map. The 65-vertex Doro–Hall graph has a separate Lean-checked
edge coloring, using the [published adjacency data](https://www.math.mun.ca/distanceregular/graphs/hall65.html).
The principal proof does not use R(3,11)≤50. The alternative [two-regime theorem](N63Final.lean)
uses the bounded form of Hall only at order 63 and
[Goedgebeur–Radziszowski's R(3,11)≤50](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v20i1p30)
at order at least 64. The published Ramsey computations and Hall's classification are not replayed in Lean.
No new custom axioms, sorries, or native_decide are used in the dossier.

[ORDER63.md](ORDER63.md) explains the new density argument and local coloring.
[PROOF.md](PROOF.md) documents the original n≥64 proof.

Replay in a fresh directory with Lean 4.34.1 (5045d0056413266e57c625dcd7c365b10e377c52)
and a built Mathlib v4.34.1 checkout (d13f23b723b8a846827a245b89c10fc7d3f11612):

```sh
LEAN_BIN=/absolute/path/to/lean MATHLIB_ROOT=/absolute/path/to/mathlib4 bash replay.sh
```

## Orders 64–66, with an additional survey-listed Ramsey input

[The all-k Lean corollary for orders 63–66](N64to66.lean#L25-L34)
adds the $R(3,14)\ge67$ existence premise recorded in Radziszowski's
published survey. The original 66-vertex witness was not retrieved or
replayed. This premise is not needed for the separate order-63 proof.
See [scope and evidence](ORDER66.md) and [independent audit](ORDER66-REVIEW.md).

## Order 62: one positive core degree eliminated

[Lean link bound](N62DegreeTwelveTenSharp.lean#L16-L27) gives at most
15 edges in the core link of an ambient degree-12, core degree-10 vertex
under the stated K₄-free candidate hypotheses at every order at least 62.
This rules out all positive-score links in that core-degree row without
an external Ramsey premise or SAT proof. The core-degree-9 positive
rows still require work, and order 62 is not resolved.
[Proof and replay](ORDER62-R10.md) · [independent audit](ORDER62-R10-REVIEW.md).

## Order 64 with a checked explicit witness

The [exact order-64 proof](N64FullOrder.lean#L10-L18) replaces the
survey-listed R(3,14) ≥ 67 premise at this order with a kernel-checked
64-vertex graph. The existing R(3,10) ≤ 41 and Hall premises remain.
The survey corollary above continues to cover orders 65–66 conditionally.
See [proof scope and replay](ORDER64.md).
