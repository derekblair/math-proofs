import N63AllK
import MixedAnalyticFinished

namespace Erdős151.H13
open Erdos151H12
open H13PetersenComponents H13MixedComponents

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem ten_template_obligation_certified : TenTemplateObligation (V:=V) := by
  intro C _ cs ci ct
  exact actual_ten_template moore_ten_verified C cs ci ct

/-- Erdős #151 at order 63, for K₄-free graphs with H(63)≥13.
The external theorems are Angeltveit's R(3,10)≤41 and the
order-at-most-63 consequence of Hall's locally Petersen classification. -/
theorem erdos151_k4free_H13_order63 (G : V → V → Prop)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41≤n → H10.TriangleIndependentTen (Fin n))
    (n63 : Fintype.card V=63) (hall : HallProjection63.{u})
    (H : TriangleIndependentAtLeast 13 V) :
    ∃ T : Finset V, T.card ≤ Fintype.card V-13 ∧
      ∀ Q, MaximalNontrivialClique G Q → ∃ x∈Q, x∈T :=
  erdos151_k4free_H13_order63_of_ten_templates G sym irr link R41 n63 hall ten_template_obligation_certified H

/-- The combined H(n)=13 slice at all orders at least 63.
R(3,11)≤50 is used only in the independent order-at-least-64 case. -/
theorem erdos151_k4free_H13_at_least63 (G : V → V → Prop)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41≤n → H10.TriangleIndependentTen (Fin n))
    (R50 : ∀ n, 50≤n → TriangleIndependentEleven (Fin n))
    (n63 : 63≤Fintype.card V) (hall : HallProjection63.{u})
    (H : TriangleIndependentAtLeast 13 V) :
    ∃ T : Finset V, T.card ≤ Fintype.card V-13 ∧
      ∀ Q, MaximalNontrivialClique G Q → ∃ x∈Q, x∈T := by
  by_cases q : Fintype.card V=63
  · exact erdos151_k4free_H13_order63 G sym irr link R41 q hall H
  · exact erdos151_k4free_H13_at_least64 G sym irr link R41 R50 (by omega) H

#print axioms erdos151_k4free_H13_order63
#print axioms erdos151_k4free_H13_at_least63
end Erdős151.H13
