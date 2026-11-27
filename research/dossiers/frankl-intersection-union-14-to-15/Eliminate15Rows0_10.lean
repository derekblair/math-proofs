import Eliminate15FastRows

namespace IU.IU15Tree
open IU.Eliminate
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem row0_10_0 : RowIsSound 0 10 ⟨6847,[2995,3475,3116,3155,3248,3317,3332,3369,3440,3456,3459,3486,3493,3498,3504]⟩ := row_fast_sound (by decide +kernel)
theorem row0_10_1 : RowIsSound 0 10 ⟨5087,[4092,4093,4094,4095,4096,4097,4098,4099,4100,4101,4102,4103,4104,4105,777]⟩ := row_fast_sound (by decide +kernel)
theorem row0_10_2 : RowIsSound 0 10 ⟨3935,[3936,4092,4093,4096,4097,4098,4100,4101,4102,4103,4104,649,3972,4019,4025]⟩ := row_fast_sound (by decide +kernel)
theorem rows0_10 : ∀ r∈max0_10, RowIsSound 0 10 r := by
  intro r hr
  simp only [max0_10,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h|hr
  · exact h.symm ▸ row0_10_0
  rcases hr with h|hr
  · exact h.symm ▸ row0_10_1
  exact hr.symm ▸ row0_10_2
end IU.IU15Tree
