import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat

/-!
# Boriboon–Kittipassorn, Conjecture 4 (arXiv:2508.17569): statement

S. Boriboon and T. Kittipassorn, *A Size Condition for Small Diameter Orientable Graphs*,
[arXiv:2508.17569v1](https://arxiv.org/abs/2508.17569v1). For `2 ≤ d ≤ n - 2`, `m(n,d)` is the
least `M` such that every bridgeless graph of order `n` and size at least `M` has an orientation
of diameter at most `d`. Conjecture 4 states `m(n,d) = C(n-d,2) + n + 2`.

These definitions repeat, verbatim, the ones in the formal-conjectures statement file
`FormalConjectures/Arxiv/2508.17569/OrientedDiameterSize.lean`. The only change is that the
orientation predicate `Digraph.IsOrientation` (defined in formal-conjectures'
`FormalConjecturesForMathlib/Combinatorics/Digraph/Tournament.lean`, not in Mathlib) is copied
here as `IsOrientation`, with the same body.
-/

namespace Arxiv2508_17569

open SimpleGraph

variable {V : Type*}

/-- A graph is bridgeless if it is connected and has no bridge. -/
def IsBridgeless (G : SimpleGraph V) : Prop := G.Connected ∧ ∀ e, ¬ G.IsBridge e

/-- Copy of formal-conjectures' `Digraph.IsOrientation D H`: `D` directs each edge of `H` in
exactly one direction and has no other arcs. -/
def IsOrientation (D : Digraph V) (H : SimpleGraph V) : Prop :=
  (∀ u v, D.Adj u v → H.Adj u v) ∧ (∀ u v, H.Adj u v → (D.Adj u v ↔ ¬ D.Adj v u))

/-- `relPow r k u v`: there is a directed walk of length exactly `k` from `u` to `v`. -/
def relPow (r : V → V → Prop) : ℕ → V → V → Prop
  | 0 => fun u v => u = v
  | k + 1 => fun u w => ∃ v, relPow r k u v ∧ r v w

/-- `G` has an orientation of diameter at most `d`. -/
def HasOrientedDiameterLE (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ D : Digraph V, IsOrientation D G ∧ ∀ u v, ∃ k ≤ d, relPow D.Adj k u v

/-- `m(n,d)`: the least `M` such that every bridgeless graph of order `n` and size at least `M`
has an orientation of diameter at most `d`. -/
noncomputable def minEdges (n d : ℕ) : ℕ :=
  sInf {M : ℕ | ∀ G : SimpleGraph (Fin n), IsBridgeless G → M ≤ G.edgeSet.ncard →
    HasOrientedDiameterLE G d}

/-- Conjecture 4 of the paper, as stated there. -/
def Conjecture4 : Prop :=
  ∀ n d : ℕ, 2 ≤ d → d ≤ n - 2 → minEdges n d = (n - d).choose 2 + n + 2

end Arxiv2508_17569
