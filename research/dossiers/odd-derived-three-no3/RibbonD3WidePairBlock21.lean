import RibbonD3WidePairCheck21
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock21 (i : Fin 30) : let z := pairLabel (⟨630+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked630
  · exact pairChecked631
  · exact pairChecked632
  · exact pairChecked633
  · exact pairChecked634
  · exact pairChecked635
  · exact pairChecked636
  · exact pairChecked637
  · exact pairChecked638
  · exact pairChecked639
  · exact pairChecked640
  · exact pairChecked641
  · exact pairChecked642
  · exact pairChecked643
  · exact pairChecked644
  · exact pairChecked645
  · exact pairChecked646
  · exact pairChecked647
  · exact pairChecked648
  · exact pairChecked649
  · exact pairChecked650
  · exact pairChecked651
  · exact pairChecked652
  · exact pairChecked653
  · exact pairChecked654
  · exact pairChecked655
  · exact pairChecked656
  · exact pairChecked657
  · exact pairChecked658
  · exact pairChecked659
end RibbonD3WideFinite
