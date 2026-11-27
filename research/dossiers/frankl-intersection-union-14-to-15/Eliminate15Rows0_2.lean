import Eliminate15Structured

namespace IU.IU15Tree
open IU.Eliminate
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem row0_2_0 : RowIsSound 0 2 ⟨3,[3190,3191,3194,3196,3198,3203,3229,3250,3262,3264,3270,3277,3285,3288,3290]⟩ := by decide +kernel
theorem rows0_2 : ∀ r∈max0_2, RowIsSound 0 2 r := by
  intro r hr
  simp only [max0_2,List.mem_cons,List.not_mem_nil,or_false] at hr
  exact hr.symm ▸ row0_2_0
theorem piv2 : PivotFacts 2 := by decide +kernel
end IU.IU15Tree
