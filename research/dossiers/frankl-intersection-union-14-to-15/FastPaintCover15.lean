import WeightData15
import Eliminate15TreeCert16

namespace IU.IU15Tree
open IU.Eliminate
set_option maxRecDepth 24000
set_option maxHeartbeats 0

theorem fast_mask_exact : vertexMask IU.IUW15.tab 15 2 2 = rootMaskLit := by decide +kernel

theorem paint_cover {a : Nat} (v : a∈admissible 15 2 2) : rootMaskLit.testBit a=true := by
  have f := vertex_mask_bit (T:=IU.IUW15.tab) (n:=15) (p:=2) (q:=2) (a:=a) IU.IUW15.tab_ok
  rw [fast_mask_exact] at f
  obtain ⟨hr, hv⟩ := List.mem_filter.mp v
  rw [f]
  exact decide_eq_true ⟨List.mem_range.mp hr,hv⟩

#print axioms paint_cover
end IU.IU15Tree
