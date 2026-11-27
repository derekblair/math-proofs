import RibbonD3WidePairCheck0
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock0 (i : Fin 30) : let z := pairLabel (⟨0+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked0
  · exact pairChecked1
  · exact pairChecked2
  · exact pairChecked3
  · exact pairChecked4
  · exact pairChecked5
  · exact pairChecked6
  · exact pairChecked7
  · exact pairChecked8
  · exact pairChecked9
  · exact pairChecked10
  · exact pairChecked11
  · exact pairChecked12
  · exact pairChecked13
  · exact pairChecked14
  · exact pairChecked15
  · exact pairChecked16
  · exact pairChecked17
  · exact pairChecked18
  · exact pairChecked19
  · exact pairChecked20
  · exact pairChecked21
  · exact pairChecked22
  · exact pairChecked23
  · exact pairChecked24
  · exact pairChecked25
  · exact pairChecked26
  · exact pairChecked27
  · exact pairChecked28
  · exact pairChecked29
end RibbonD3WideFinite
