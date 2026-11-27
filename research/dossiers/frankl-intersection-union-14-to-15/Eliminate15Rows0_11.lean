import Eliminate15FastRows

namespace IU.IU15Tree
open IU.Eliminate
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem row0_11_0 : RowIsSound 0 11 ⟨5119,[4092,4093,4094,4095,4096,4097,4098,4099,4100,4101,4102,4103,4104,4105,800]⟩ := row_fast_sound (by decide +kernel)
theorem row0_11_1 : RowIsSound 0 11 ⟨3967,[3936,4092,4093,4096,4097,4098,4100,4101,4102,4103,4104,3911,3918,3919,3920]⟩ := row_fast_sound (by decide +kernel)
theorem rows0_11 : ∀ r∈max0_11, RowIsSound 0 11 r := by
  intro r hr
  simp only [max0_11,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h|hr
  · exact h.symm ▸ row0_11_0
  exact hr.symm ▸ row0_11_1
end IU.IU15Tree
