import Eliminate15FastRows

namespace IU.IU15Tree
open IU.Eliminate
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem row1_8_0 : RowIsSound 1 8 ⟨1935,[1820,3248,3104,3137,3152,3216,3230,3241,3252,3279,3284,3127,3134,3153,3173]⟩ := row_fast_sound (by decide +kernel)
theorem rows1_8 : ∀ r∈max1_8, RowIsSound 1 8 r := by
  intro r hr
  simp only [max1_8,List.mem_cons,List.not_mem_nil,or_false] at hr
  exact hr.symm ▸ row1_8_0
theorem piv8 : PivotFacts 8 := by decide +kernel
end IU.IU15Tree
