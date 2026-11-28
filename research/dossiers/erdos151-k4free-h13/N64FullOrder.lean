import N64CheckedWitnessBridge
import New64Endpoint

namespace Erdős151.H13
open Erdos151H12 H13PetersenComponents
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Order-64 K₄-free Erdős #151, with the upper bound on H(64)
checked from an explicit 64-vertex graph. The only external
premises are R(3,10)≤41 and Hall's locally Petersen classification. -/
theorem erdos151_k4free_order64 (G : V → V → Prop)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41≤n → H10.TriangleIndependentTen (Fin n))
    (n64 : Fintype.card V=64) (hall : HallProjectionAll.{u})
    (k : ℕ) (H : TriangleIndependentAtLeast k V) :
    ∃ T : Finset V, T.card ≤ Fintype.card V-k ∧
      ∀ Q, MaximalNontrivialClique G Q → ∃ x∈Q, x∈T :=
  erdos151_k4free_order64_from_witness G sym irr link R41 n64 hall
    Erdos151Ramsey.New64.not_universal14 k H

#print axioms erdos151_k4free_order64
end Erdős151.H13
