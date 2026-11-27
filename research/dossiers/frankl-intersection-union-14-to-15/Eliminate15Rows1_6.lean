import Eliminate15FastRows

namespace IU.IU15Tree
open IU.Eliminate
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem row1_6_0 : RowIsSound 1 6 ⟨455,[4094,4096,4097,4104,4105,2225,3496,3982,3983,3984,3985,3986,3987,4017,4021]⟩ := row_fast_sound (by decide +kernel)
theorem rows1_6 : ∀ r∈max1_6, RowIsSound 1 6 r := by
  intro r hr
  simp only [max1_6,List.mem_cons,List.not_mem_nil,or_false] at hr
  exact hr.symm ▸ row1_6_0
theorem piv6 : PivotFacts 6 := by decide +kernel
end IU.IU15Tree
