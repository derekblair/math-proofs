import New64Graph
import New64Numeric

namespace Erdos151Ramsey.New64
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem alpha_le_thirteen (S : Finset (Fin 64)) (ind : Independent graph S) : S.card ≤ 13 := by
  by_cases h : extra ∈ S
  · have sub : S.erase extra ⊆ vv checkRoot := by
      intro x hx
      obtain ⟨nx, hx⟩ := Finset.mem_erase.mp hx
      have no : adj extra x = false := Bool.eq_false_iff.mpr (ind extra h x hx)
      simp [vv, checkRoot, removes_spec, notAdjacent_spec, nx.symm, no]
    have i : Independent graph (S.erase extra) :=
      fun a ha b hb => ind a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
    have bound := check_sound _ _ _ checked_root _ sub i
    have eq := Finset.card_erase_add_one h
    omega
  · exact old_bound S h ind

theorem ramsey314_ge65 :
    ∃ R : Fin 64 → Fin 64 → Prop, (∀ {a b}, R a b → R b a) ∧ (∀ a, ¬ R a a) ∧
      TriangleFree R ∧ (∀ S : Finset (Fin 64), Independent R S → S.card ≤ 13) :=
  ⟨graph, @graph_symm, graph_irrefl, graph_triangle_free, alpha_le_thirteen⟩

theorem not_universal14 :
    ¬ (∀ R : Fin 64 → Fin 64 → Prop, (∀ {a b}, R a b → R b a) → (∀ a, ¬ R a a) →
      TriangleFree R → ∃ S : Finset (Fin 64), 14 ≤ S.card ∧ Independent R S) := by
  intro h
  obtain ⟨S, hs, hI⟩ := h graph @graph_symm graph_irrefl graph_triangle_free
  have := alpha_le_thirteen S hI
  omega

#print axioms ramsey314_ge65
#print axioms not_universal14
end Erdos151Ramsey.New64
