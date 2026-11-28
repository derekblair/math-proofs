import N63AllK
import H13AtLeast63Hall

namespace Erdős151.H13
open Finset Erdos151H12 Erdos151Ramsey H13PetersenComponents

private theorem transport_to_larger {V W : Type*} [Fintype V] [Fintype W]
    (k : Nat) (e : V ↪ W) (H : TriangleIndependentAtLeast k V) :
    TriangleIndependentAtLeast k W := by
  classical
  intro G sym irr tf
  obtain ⟨S,sz,ind⟩ := H (fun a b=>G (e a) (e b))
    (fun {_ _} h=>sym h) (fun a=>irr _) (fun _ _ _ ab bc ac=>tf _ _ _ ab bc ac)
  refine ⟨S.map e,by simpa using sz,?_⟩
  intro a ha b hb
  obtain ⟨x,hx,rfl⟩ := mem_map.mp ha
  obtain ⟨y,hy,rfl⟩ := mem_map.mp hb
  exact ind x hx y hy

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Order-64 K₄-free Erdős #151 with an arbitrary explicit witness
ruling out a guaranteed independent 14 on Fin 64. -/
theorem erdos151_k4free_order64_from_witness
    (G : V → V → Prop)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41≤n → H10.TriangleIndependentTen (Fin n))
    (n64 : Fintype.card V=64)
    (hall : HallProjectionAll.{u})
    (ramsey64 : ¬ TriangleIndependentAtLeast 14 (Fin 64))
    (k : ℕ) (H : TriangleIndependentAtLeast k V) :
    ∃ T : Finset V, T.card ≤ Fintype.card V-k ∧
      ∀ Q, MaximalNontrivialClique G Q → ∃ x∈Q, x∈T := by
  have k13 : k≤13 := by
    by_contra! h
    let e := (Fintype.equivFinOfCardEq n64).toEmbedding
    exact ramsey64 (transport_to_larger 14 e (triangle_independent_mono_n63 14 k h H))
  by_cases k10 : k≤10
  · have h10 := Erdős151.H12.triangle_independent_ten_transport
      (Fintype.equivFin V) (R41 _ (by omega))
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
  exact erdos151_k4free_H13_at_least63_of_hall_all G sym irr link R41 (by omega) hall H

#print axioms erdos151_k4free_order64_from_witness
end Erdős151.H13
