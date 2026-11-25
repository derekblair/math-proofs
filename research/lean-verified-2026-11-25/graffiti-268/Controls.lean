import Result

namespace Wow268

local notation "K₂" => (⊤ : SimpleGraph (Fin 2))

theorem k2_average : avg K₂ = 1 := by
  classical
  have hpair : centerPairs K₂ = {((0,1) : Fin 2 × Fin 2), (1,0)} := by
    ext p
    rw [member_centerPairs]
    rcases p with ⟨a,b⟩
    have hc (u : Fin 2) : u ∈ (K₂).center :=
      ((K₂).mem_center_iff u).mpr (by simp [SimpleGraph.eccent_top, SimpleGraph.radius_top])
    simp only [Prod.fst, Prod.snd, hc, true_and]
    fin_cases a <;> fin_cases b <;> decide
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hp : ((0,1) : Fin 2 × Fin 2) ≠ (1,0) := by decide
  simp [avg, hpair, hp, SimpleGraph.dist_top_of_ne, h01, h10]

theorem k2_floor : ⌊1 + avg K₂⌋ = (2 : ℤ) := by
  rw [k2_average]
  norm_num

theorem k2_shifted_false : ¬ ⌊2 + avg K₂⌋ ≤ (2 : ℤ) := by
  rw [k2_average]
  norm_num

#print axioms Wow268.k2_shifted_false

end Wow268
