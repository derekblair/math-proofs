import N63Final
import Seed64Endpoint

namespace Erdős151.H13
open Erdos151H12
open H13PetersenComponents

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Full K₄-free slice of Erdős #151 on exactly 63 vertices.
This quantifies over every triangle-free guarantee k, hence in
particular over the optimal k=H(63), without assuming its exact value.
The published 63-vertex circulant excludes k≥14 in Lean. The only
external theorem inputs are Angeltveit's R(3,10)≤41 and Hall's
order-at-most-63 locally Petersen recognition consequence. -/
theorem erdos151_k4free_order63 (G : V → V → Prop)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41≤n → H10.TriangleIndependentTen (Fin n))
    (n63 : Fintype.card V=63) (hall : HallProjection63.{u})
    (k : ℕ) (H : TriangleIndependentAtLeast k V) :
    ∃ T : Finset V, T.card ≤ Fintype.card V-k ∧
      ∀ Q, MaximalNontrivialClique G Q → ∃ x∈Q, x∈T :=
  erdos151_k4free_order63_all_k_of_ten_templates G sym irr link R41 n63 hall
    ten_template_obligation_certified Erdos151Ramsey.Seed64.not_universal14 k H

#print axioms erdos151_k4free_order63
end Erdős151.H13
