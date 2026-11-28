import MaskSearch64

namespace Erdos151Ramsey.Seed64
set_option maxRecDepth 8192
set_option maxHeartbeats 0
instance graph_dec : DecidableRel graph := fun a b => inferInstanceAs (Decidable (adj a b = true))

theorem graph_symm {a b : Fin 63} (ab : graph a b) : graph b a := by
  have test : ∀ b : Fin 63, graph 0 b → graph b 0 := by
    decide +kernel
  have z : graph 0 (b-a) := by
    have h := adj_shift a b a
    rw [sub_self] at h
    unfold graph at ab ⊢
    exact h.trans ab
  have h := adj_shift b a a
  rw [sub_self] at h
  exact h.symm.trans (test _ z)

theorem graph_triangle_free : TriangleFree graph := by
  apply triangle_rooted
  decide +kernel

def alphaWitness : Finset (Fin 63) := {0,1,6,8,13,14,19,24,32,37,42,43,50}

theorem alphaWitness_card : alphaWitness.card = 13 := by decide +kernel

theorem alphaWitness_ind : Independent graph alphaWitness := by
  change ∀ a ∈ alphaWitness, ∀ b ∈ alphaWitness, ¬ graph a b
  decide +kernel

end Erdos151Ramsey.Seed64
