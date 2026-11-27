import RibbonD3WidePairCheck19
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock19 (i : Fin 30) : let z := pairLabel (⟨570+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked570
  · exact pairChecked571
  · exact pairChecked572
  · exact pairChecked573
  · exact pairChecked574
  · exact pairChecked575
  · exact pairChecked576
  · exact pairChecked577
  · exact pairChecked578
  · exact pairChecked579
  · exact pairChecked580
  · exact pairChecked581
  · exact pairChecked582
  · exact pairChecked583
  · exact pairChecked584
  · exact pairChecked585
  · exact pairChecked586
  · exact pairChecked587
  · exact pairChecked588
  · exact pairChecked589
  · exact pairChecked590
  · exact pairChecked591
  · exact pairChecked592
  · exact pairChecked593
  · exact pairChecked594
  · exact pairChecked595
  · exact pairChecked596
  · exact pairChecked597
  · exact pairChecked598
  · exact pairChecked599
end RibbonD3WideFinite
