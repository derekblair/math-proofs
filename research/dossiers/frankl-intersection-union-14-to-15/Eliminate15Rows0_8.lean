import Eliminate15Structured

namespace IU.IU15Tree
open IU.Eliminate
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem row0_8_0 : RowIsSound 0 8 ⟨14479,[3275,3398,3466,3490,3495,127,3248,3265,3292,3456,3498,3504,3252,3260,3279]⟩ := by decide +kernel
theorem row0_8_1 : RowIsSound 0 8 ⟨11023,[3460,3248,3292,3331,3391,3393,3436,3456,3498,3504,440,3252,3260,3279,3302]⟩ := by decide +kernel
theorem row0_8_2 : RowIsSound 0 8 ⟨10903,[3198,3234,2830,2854,2949,3001,3248,3254,3292,3312,3456,3486,3498,3504,568]⟩ := by decide +kernel
theorem row0_8_3 : RowIsSound 0 8 ⟨7319,[3466,3495,184,3057,3248,3456,3486,3498,3504,3059,3083,3087,3090,3158,3182]⟩ := by decide +kernel
theorem row0_8_4 : RowIsSound 0 8 ⟨6935,[3032,3240,3388,3460,6,3223,3248,3331,3456,3458,3486,3498,3504,3059,3083]⟩ := by decide +kernel
theorem row0_8_5 : RowIsSound 0 8 ⟨6823,[2995,3475,3116,3248,3317,3332,3456,3459,3486,3498,3504,451,3059,3083,3087]⟩ := by decide +kernel
theorem row0_8_6 : RowIsSound 0 8 ⟨3911,[3935,3936,3937,4096,4097,4104,2076,3953,3954,3960,3961,3965,3966,3967,3970]⟩ := by decide +kernel
theorem row0_8_7 : RowIsSound 0 8 ⟨6811,[336,3248,3456,3486,3493,3498,3504,3059,3083,3087,3090,3158,3182,3252,3260]⟩ := by decide +kernel
theorem row0_8_8 : RowIsSound 0 8 ⟨5081,[4092,4093,4094,4095,4096,4097,4098,4099,4100,4101,4102,4103,4104,4105,3050]⟩ := by decide +kernel
theorem rows0_8 : ∀ r∈max0_8, RowIsSound 0 8 r := by
  intro r hr
  simp only [max0_8,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h|hr
  · exact h.symm ▸ row0_8_0
  rcases hr with h|hr
  · exact h.symm ▸ row0_8_1
  rcases hr with h|hr
  · exact h.symm ▸ row0_8_2
  rcases hr with h|hr
  · exact h.symm ▸ row0_8_3
  rcases hr with h|hr
  · exact h.symm ▸ row0_8_4
  rcases hr with h|hr
  · exact h.symm ▸ row0_8_5
  rcases hr with h|hr
  · exact h.symm ▸ row0_8_6
  rcases hr with h|hr
  · exact h.symm ▸ row0_8_7
  exact hr.symm ▸ row0_8_8
end IU.IU15Tree
