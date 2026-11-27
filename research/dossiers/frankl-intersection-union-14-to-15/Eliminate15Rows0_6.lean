import Eliminate15Structured

namespace IU.IU15Tree
open IU.Eliminate
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem row0_6_0 : RowIsSound 0 6 ⟨839,[3935,3936,3937,4094,4096,4097,4104,4105,3940,3941,3942,3943,3944,3945,3946]⟩ := by decide +kernel
theorem row0_6_1 : RowIsSound 0 6 ⟨473,[4092,4093,4094,4095,4096,4097,4098,4099,4100,4101,4102,4103,4104,4105,3089]⟩ := by decide +kernel
theorem rows0_6 : ∀ r∈max0_6, RowIsSound 0 6 r := by
  intro r hr
  simp only [max0_6,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h|hr
  · exact h.symm ▸ row0_6_0
  exact hr.symm ▸ row0_6_1
end IU.IU15Tree
