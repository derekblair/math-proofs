import Eliminate15FastRows

namespace IU.IU15Tree
open IU.Eliminate
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem row0_12_0 : RowIsSound 0 12 ⟨4095,[3936,4092,4093,4096,4097,4098,4100,4101,4102,4103,4104,2124,3911,3918,3919]⟩ := row_fast_sound (by decide +kernel)
theorem rows0_12 : ∀ r∈max0_12, RowIsSound 0 12 r := by
  intro r hr
  simp only [max0_12,List.mem_cons,List.not_mem_nil,or_false] at hr
  exact hr.symm ▸ row0_12_0
theorem piv12 : PivotFacts 12 := by decide +kernel
end IU.IU15Tree
