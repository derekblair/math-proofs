import Eliminate15FastRows

namespace IU.IU15Tree
open IU.Eliminate
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem row0_13_0 : RowIsSound 0 13 ⟨8191,[2995,3005,3007,3032,3053,3068,3094,3107,3115,3154,3161,3181,3186,3189,3196]⟩ := row_fast_sound (by decide +kernel)
theorem rows0_13 : ∀ r∈max0_13, RowIsSound 0 13 r := by
  intro r hr
  simp only [max0_13,List.mem_cons,List.not_mem_nil,or_false] at hr
  exact hr.symm ▸ row0_13_0
theorem piv13 : PivotFacts 13 := by decide +kernel
end IU.IU15Tree
