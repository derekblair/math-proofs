import Eliminate15FastRows

namespace IU.IU15Tree
open IU.Eliminate
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem row1_9_0 : RowIsSound 1 9 ⟨1951,[2726,3071,3248,3063,3082,3083,3087,3090,3104,3137,3152,3216,3230,3241,3252]⟩ := row_fast_sound (by decide +kernel)
theorem rows1_9 : ∀ r∈max1_9, RowIsSound 1 9 r := by
  intro r hr
  simp only [max1_9,List.mem_cons,List.not_mem_nil,or_false] at hr
  exact hr.symm ▸ row1_9_0
theorem piv9 : PivotFacts 9 := by decide +kernel
end IU.IU15Tree
