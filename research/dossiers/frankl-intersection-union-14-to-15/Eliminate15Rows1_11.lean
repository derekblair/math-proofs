import Eliminate15FastRows

namespace IU.IU15Tree
open IU.Eliminate
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem row1_11_0 : RowIsSound 1 11 ⟨2047,[4093,4098,4100,4104,230,787,800,3071,3248,3340,3372,3378,3514,3991,3992]⟩ := row_fast_sound (by decide +kernel)
theorem rows1_11 : ∀ r∈max1_11, RowIsSound 1 11 r := by
  intro r hr
  simp only [max1_11,List.mem_cons,List.not_mem_nil,or_false] at hr
  exact hr.symm ▸ row1_11_0
theorem piv11 : PivotFacts 11 := by decide +kernel
end IU.IU15Tree
