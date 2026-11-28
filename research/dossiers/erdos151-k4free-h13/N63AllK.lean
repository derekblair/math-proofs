import N63FinalBridge
import H13Final64

namespace Erdős151.H13
open Erdos151H12 Erdos151Ramsey
open H13PetersenComponents

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {W : Type*} [Fintype W]

theorem triangle_independent_transport_n63 (k : ℕ) (e : V ≃ W)
    (H : TriangleIndependentAtLeast k V) : TriangleIndependentAtLeast k W := by
  classical
  intro G sym irr tri
  let R (a b : V) := G (e a) (e b)
  obtain ⟨S,hS,hi⟩ := H R (fun {_ _} h=>sym h) (fun _ h=>irr _ h)
    (fun _ _ _ ab bc ac => tri _ _ _ ab bc ac)
  refine ⟨S.map e.toEmbedding,by simpa using hS,?_⟩
  intro a ha b hb
  obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hb
  exact hi x hx y hy

theorem triangle_independent_mono_n63 (k m : ℕ) (h : k≤m)
    (H : TriangleIndependentAtLeast m V) : TriangleIndependentAtLeast k V := by
  intro G sym irr tri
  obtain ⟨S,hS,hi⟩ := H G (fun {_ _} h=>sym h) irr tri
  exact ⟨S,h.trans hS,hi⟩

/-- Once a published order-63 witness rules out H(63)≥14, the H=13
advance and earlier cases cover every possible H(63). -/
theorem erdos151_k4free_order63_all_k_of_ten_templates (G : V → V → Prop)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41≤n → H10.TriangleIndependentTen (Fin n))
    (n63 : Fintype.card V=63) (hall : HallProjection63.{u})
    (local10 : TenTemplateObligation (V:=V))
    (witness : ¬ TriangleIndependentAtLeast 14 (Fin 63))
    (k : ℕ) (H : TriangleIndependentAtLeast k V) :
    ∃ T : Finset V, T.card ≤ Fintype.card V-k ∧
      ∀ Q, MaximalNontrivialClique G Q → ∃ x∈Q, x∈T := by
  have k13 : k≤13 := by
    by_contra! h
    exact witness (triangle_independent_transport_n63 14
      (Fintype.equivFinOfCardEq n63) (triangle_independent_mono_n63 14 k h H))
  by_cases k10 : k≤10
  · have h10 := Erdős151.H12.triangle_independent_ten_transport
      (Fintype.equivFinOfCardEq n63) (R41 63 (by decide))
    obtain ⟨S,hs,hf⟩ := H10.k4free_of_triangle_independent_ten G sym irr link (by omega) h10
    exact free_set_to_maximal_clique_transversal G k sym irr link S (k10.trans hs) hf
  by_cases k11 : k=11
  · subst k
    obtain ⟨S,hs,hf⟩ := k4free_of_triangle_independent_eleven G sym irr link (by omega) H
    exact free_set_to_maximal_clique_transversal G 11 sym irr link S hs hf
  by_cases k12 : k=12
  · subst k
    exact Erdős151.H12.erdos151_k4free_H12_of_Ramsey41 G sym irr link R41 H
  have eq : k=13 := by omega
  subst k
  exact erdos151_k4free_H13_order63_of_ten_templates G sym irr link R41 n63 hall local10 H

#print axioms erdos151_k4free_order63_all_k_of_ten_templates
end Erdős151.H13
