import RibbonD3WidePairCheck22
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock22 (i : Fin 30) : let z := pairLabel (⟨660+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked660
  · exact pairChecked661
  · exact pairChecked662
  · exact pairChecked663
  · exact pairChecked664
  · exact pairChecked665
  · exact pairChecked666
  · exact pairChecked667
  · exact pairChecked668
  · exact pairChecked669
  · exact pairChecked670
  · exact pairChecked671
  · exact pairChecked672
  · exact pairChecked673
  · exact pairChecked674
  · exact pairChecked675
  · exact pairChecked676
  · exact pairChecked677
  · exact pairChecked678
  · exact pairChecked679
  · exact pairChecked680
  · exact pairChecked681
  · exact pairChecked682
  · exact pairChecked683
  · exact pairChecked684
  · exact pairChecked685
  · exact pairChecked686
  · exact pairChecked687
  · exact pairChecked688
  · exact pairChecked689
end RibbonD3WideFinite
