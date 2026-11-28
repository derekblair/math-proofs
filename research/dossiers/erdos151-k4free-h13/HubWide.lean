import HubDomains

namespace Erdos151H13
open Erdős151 Erdos151H12 Erdos151Ramsey

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

/-- When the overlap discount C+s is at least ten, the outer pool alone
completes the three-hub argument for order≥64 and total hub degree≤36.
This is the wide-overlap arm of the new insertion lemma. -/
theorem wide_three_hub_free13
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41 ≤ n → Erdős151.H10.TriangleIndependentTen (Fin n))
    (sub : ∀ a b, C a b → G a b)
    (coreNonlone : ∀ a b, C a b → ¬ Lone G a b)
    (x w y : V) (cxw : C x w) (cyw : C y w) (hxy : ¬ G x y) (xyne : x ≠ y)
    (rx : 8 ≤ (neighbors C x).card) (ry : 8 ≤ (neighbors C y).card)
    (n : 64 ≤ Fintype.card V)
    (D : (neighbors G x).card + (neighbors G y).card + (neighbors G w).card ≤ 36)
    (wide : 10 ≤ (neighbors G x∩neighbors G w).card +
      (neighbors G y∩neighbors G w).card +
      ((neighbors G x∩neighbors G y)\insert w (neighbors G w)).card) :
    ∃ T : Finset V, 13 ≤ T.card ∧ Free (Forbidden G) (T : Set V) := by
  classical
  let H := (neighbors G x∩neighbors G w).card +
      (neighbors G y∩neighbors G w).card +
      ((neighbors G x∩neighbors G y)\insert w (neighbors G w)).card
  let E := outerCandidates G x w y
  have ws : 10 ≤ H := wide
  have eCard := outer_candidates_size G C sub coreNonlone x w y
  have c : 14 ≤ E.card + H := by
    dsimp [E,H]
    omega
  let P := pairConflict G x y
  have ps : ∀ {a b}, P a b → P b a := fun e =>
    ⟨sym e.1,e.2.elim (fun h => Or.inl ⟨h.2,h.1⟩) (fun h => Or.inr ⟨h.2,h.1⟩)⟩
  have pi (a : V) : ¬ P a a := fun e => irr a e.1
  have pt : TriangleFree P := pairConflict_triangleFree G x y link
  have yield : ∃ B ⊆ E, 12 ≤ H + B.card ∧ Independent P B := by
    by_cases h12 : 12 ≤ H
    · exact ⟨∅,Finset.empty_subset _,by simpa using h12,by simp [Independent]⟩
    by_cases h11 : 11 ≤ H
    · obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < E.card by omega)
      refine ⟨{v},Finset.singleton_subset_iff.mpr hv,by simp; omega,?_⟩
      intro a ha b hb
      simp only [Finset.mem_singleton] at ha hb
      subst a
      subst b
      exact pi _
    obtain ⟨B,hB,bCard,ind⟩ := independent_two_of_three P ps pi pt E (by omega)
    exact ⟨B,hB,by omega,ind⟩
  obtain ⟨B,bs,bc,bi⟩ := yield
  have hxw := sub x w cxw
  have hyw := sub y w cyw
  refine free13_of_three_hub_budget G sym irr link R41 x w y hxw (sym hyw) hxy xyne
    (coreNonlone x w cxw) (coreNonlone y w cyw) ∅ B (by simp)
    (fun a ha => outer_candidates_eligible G x w y a (bs ha)) (by simp) bi ?_ ?_
  · intro a ha
    have hb : a∈B := by simpa using ha
    exact candidate_pools_inside G C sub irr x w y (sym hxw) (sym hyw)
      (Finset.mem_union_right _ (bs hb))
  · simp only [Finset.empty_union]
    dsimp only [H] at bc
    omega

#print axioms wide_three_hub_free13
end Erdos151H13
