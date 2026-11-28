import N64to66
import Archive66Endpoint

namespace Erdős151.H13
open Erdos151H12 H13PetersenComponents
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The K₄-free Erdős #151 bound for every order 63–66, with Kolodyazhny's
archived Ramsey graph replayed in Lean. The published Ramsey-41 and
Hall inputs remain explicit. -/
theorem erdos151_k4free_orders63_to66_with_checked_witness
    (G : V → V → Prop)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41≤n → H10.TriangleIndependentTen (Fin n))
    (n63 : 63≤Fintype.card V) (n66 : Fintype.card V≤66)
    (hall : HallProjectionAll.{u})
    (k : ℕ) (H : TriangleIndependentAtLeast k V) :
    ∃ T : Finset V, T.card ≤ Fintype.card V-k ∧
      ∀ Q, MaximalNontrivialClique G Q → ∃ x∈Q, x∈T :=
  erdos151_k4free_orders63_to66_of_published_ramsey G sym irr link R41
    n63 n66 hall Erdos151Ramsey.Archive66.not_universal14 k H

#print axioms erdos151_k4free_orders63_to66_with_checked_witness
end Erdős151.H13
