import Eliminate15FastRows

namespace IU.IU15Tree
open IU.Eliminate
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem row1_10_0 : RowIsSound 1 10 ⟨1983,[3071,3248,2595,3031,3063,3082,3083,3087,3090,3104,3137,3152,3216,3230,3241]⟩ := row_fast_sound (by decide +kernel)
theorem rows1_10 : ∀ r∈max1_10, RowIsSound 1 10 r := by
  intro r hr
  simp only [max1_10,List.mem_cons,List.not_mem_nil,or_false] at hr
  exact hr.symm ▸ row1_10_0
theorem piv10 : PivotFacts 10 := by decide +kernel
end IU.IU15Tree
