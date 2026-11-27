import Eliminate15Structured

namespace IU.IU15Tree
open IU.Eliminate
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem row0_4_0 : RowIsSound 0 4 ⟨71,[3935,3936,3937,4094,4096,4097,4104,4105,3940,3941,3942,3943,3944,3945,3946]⟩ := by decide +kernel
theorem rows0_4 : ∀ r∈max0_4, RowIsSound 0 4 r := by
  intro r hr
  simp only [max0_4,List.mem_cons,List.not_mem_nil,or_false] at hr
  exact hr.symm ▸ row0_4_0
theorem piv4 : PivotFacts 4 := by decide +kernel
end IU.IU15Tree
