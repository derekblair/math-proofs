import Eliminate15Structured

namespace IU.IU15Tree
open IU.Eliminate
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem row0_5_0 : RowIsSound 0 5 ⟨327,[3935,3936,3937,4094,4096,4097,4104,4105,3776,3940,3941,3942,3943,3944,3945]⟩ := by decide +kernel
theorem row0_5_1 : RowIsSound 0 5 ⟨217,[4092,4093,4094,4095,4096,4097,4098,4099,4100,4101,4102,4103,4104,4105,3970]⟩ := by decide +kernel
theorem rows0_5 : ∀ r∈max0_5, RowIsSound 0 5 r := by
  intro r hr
  simp only [max0_5,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h|hr
  · exact h.symm ▸ row0_5_0
  exact hr.symm ▸ row0_5_1
end IU.IU15Tree
