import Eliminate15FastRows

namespace IU.IU15Tree
open IU.Eliminate
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem row1_5_0 : RowIsSound 1 5 ⟨199,[4094,4096,4097,4104,4105,3496,3658,3940,3941,3942,3943,3944,3945,3946,3947]⟩ := row_fast_sound (by decide +kernel)
theorem rows1_5 : ∀ r∈max1_5, RowIsSound 1 5 r := by
  intro r hr
  simp only [max1_5,List.mem_cons,List.not_mem_nil,or_false] at hr
  exact hr.symm ▸ row1_5_0
theorem piv5 : PivotFacts 5 := by decide +kernel
end IU.IU15Tree
