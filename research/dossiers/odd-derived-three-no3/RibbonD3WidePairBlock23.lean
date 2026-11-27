import RibbonD3WidePairCheck23
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock23 (i : Fin 29) : let z := pairLabel (⟨690+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked690
  · exact pairChecked691
  · exact pairChecked692
  · exact pairChecked693
  · exact pairChecked694
  · exact pairChecked695
  · exact pairChecked696
  · exact pairChecked697
  · exact pairChecked698
  · exact pairChecked699
  · exact pairChecked700
  · exact pairChecked701
  · exact pairChecked702
  · exact pairChecked703
  · exact pairChecked704
  · exact pairChecked705
  · exact pairChecked706
  · exact pairChecked707
  · exact pairChecked708
  · exact pairChecked709
  · exact pairChecked710
  · exact pairChecked711
  · exact pairChecked712
  · exact pairChecked713
  · exact pairChecked714
  · exact pairChecked715
  · exact pairChecked716
  · exact pairChecked717
  · exact pairChecked718
end RibbonD3WideFinite
