import Eliminate15FastRows

namespace IU.IU15Tree
open IU.Eliminate
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem row1_7_0 : RowIsSound 1 7 ⟨967,[4094,4096,4097,4104,4105,1160,4017,4021,4022,4023,4024,4026,4027,4028,4031]⟩ := row_fast_sound (by decide +kernel)
theorem rows1_7 : ∀ r∈max1_7, RowIsSound 1 7 r := by
  intro r hr
  simp only [max1_7,List.mem_cons,List.not_mem_nil,or_false] at hr
  exact hr.symm ▸ row1_7_0
theorem piv7 : PivotFacts 7 := by decide +kernel
end IU.IU15Tree
