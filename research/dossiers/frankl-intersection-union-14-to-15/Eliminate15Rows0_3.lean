import Eliminate15Structured

namespace IU.IU15Tree
open IU.Eliminate
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem row0_3_0 : RowIsSound 0 3 ⟨7,[3935,3936,3937,4094,4096,4097,4104,4105,1882,3940,3941,3942,3943,3944,3945]⟩ := by decide +kernel
theorem rows0_3 : ∀ r∈max0_3, RowIsSound 0 3 r := by
  intro r hr
  simp only [max0_3,List.mem_cons,List.not_mem_nil,or_false] at hr
  exact hr.symm ▸ row0_3_0
theorem piv3 : PivotFacts 3 := by decide +kernel
end IU.IU15Tree
