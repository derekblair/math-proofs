import Seed64Graph

namespace Erdos151Ramsey.Seed64
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem alpha_of_checked {plan : Plan} (checked : check plan checkRoot 13 = true) (S : Finset (Fin 63)) (ind : Independent graph S) :
    S.card ≤ 13 := by
  refine rooted_bound (fun T hT iT => check_sound _ _ _ checked T ?_ iT) S ind
  intro u hu
  obtain ⟨hne,hno⟩ := hT u hu
  have hf : adj 0 u = false := Bool.eq_false_iff.mpr hno
  show u ∈ vv checkRoot
  simp [vv, checkRoot, removes_spec, notAdjacent_spec, hne.symm, hf]

/-- Published Furini et al. 63-vertex circulant: a triangle-free lower-bound
witness for R(3,14)≥64. The graph's adjacency is exactly their circulant
difference list, and the independent-set exclusion uses a kernel-checked search. -/
theorem ramsey314_of_checked {plan : Plan} (checked : check plan checkRoot 13 = true) :
    ∃ R : Fin 63 → Fin 63 → Prop, (∀ {a b}, R a b → R b a) ∧ (∀ a, ¬ R a a) ∧
      TriangleFree R ∧ (∀ S : Finset (Fin 63), Independent R S → S.card ≤ 13) :=
  ⟨graph, @graph_symm, graph_irrefl, graph_triangle_free, alpha_of_checked checked⟩

theorem not_universal14_of_checked {plan : Plan} (checked : check plan checkRoot 13 = true) :
    ¬ (∀ R : Fin 63 → Fin 63 → Prop, (∀ {a b}, R a b → R b a) → (∀ a, ¬ R a a) →
      TriangleFree R → ∃ S : Finset (Fin 63), 14 ≤ S.card ∧ Independent R S) := by
  intro h
  obtain ⟨S, hs, hI⟩ := h graph @graph_symm graph_irrefl graph_triangle_free
  have := alpha_of_checked checked S hI
  omega

end Erdos151Ramsey.Seed64
