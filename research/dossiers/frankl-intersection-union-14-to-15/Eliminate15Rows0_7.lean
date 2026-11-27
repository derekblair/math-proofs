import Eliminate15Structured

namespace IU.IU15Tree
open IU.Eliminate
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem row0_7_0 : RowIsSound 0 7 ⟨1863,[3935,3936,3937,4094,4096,4097,4104,4105,3013,3950,3951,3952,3953,3954,3955]⟩ := by decide +kernel
theorem row0_7_1 : RowIsSound 0 7 ⟨985,[4092,4093,4094,4095,4096,4097,4098,4099,4100,4101,4102,4103,4104,4105,446]⟩ := by decide +kernel
theorem rows0_7 : ∀ r∈max0_7, RowIsSound 0 7 r := by
  intro r hr
  simp only [max0_7,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h|hr
  · exact h.symm ▸ row0_7_0
  exact hr.symm ▸ row0_7_1
end IU.IU15Tree
