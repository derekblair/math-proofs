import Eliminate15FastRows

namespace IU.IU15Tree
open IU.Eliminate
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem row0_9_0 : RowIsSound 0 9 ⟨6815,[3248,3456,3486,3493,3498,3504,429,3059,3083,3087,3090,3158,3182,3252,3260]⟩ := row_fast_sound (by decide +kernel)
theorem row0_9_1 : RowIsSound 0 9 ⟨5967,[3936,4092,4094,4096,4097,4099,4100,4104,4105,3962,3963,3969,3972,3980,4020]⟩ := row_fast_sound (by decide +kernel)
theorem row0_9_2 : RowIsSound 0 9 ⟨3927,[3936,4092,4096,4097,4098,4100,4101,4102,4103,4104,3972,4019,4025,4051,4057]⟩ := row_fast_sound (by decide +kernel)
theorem row0_9_3 : RowIsSound 0 9 ⟨5083,[4092,4093,4094,4095,4096,4097,4098,4099,4100,4101,4102,4103,4104,4105,2364]⟩ := row_fast_sound (by decide +kernel)
theorem rows0_9 : ∀ r∈max0_9, RowIsSound 0 9 r := by
  intro r hr
  simp only [max0_9,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h|hr
  · exact h.symm ▸ row0_9_0
  rcases hr with h|hr
  · exact h.symm ▸ row0_9_1
  rcases hr with h|hr
  · exact h.symm ▸ row0_9_2
  exact hr.symm ▸ row0_9_3
end IU.IU15Tree
