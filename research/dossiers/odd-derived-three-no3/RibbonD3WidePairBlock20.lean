import RibbonD3WidePairCheck20
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock20 (i : Fin 30) : let z := pairLabel (⟨600+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked600
  · exact pairChecked601
  · exact pairChecked602
  · exact pairChecked603
  · exact pairChecked604
  · exact pairChecked605
  · exact pairChecked606
  · exact pairChecked607
  · exact pairChecked608
  · exact pairChecked609
  · exact pairChecked610
  · exact pairChecked611
  · exact pairChecked612
  · exact pairChecked613
  · exact pairChecked614
  · exact pairChecked615
  · exact pairChecked616
  · exact pairChecked617
  · exact pairChecked618
  · exact pairChecked619
  · exact pairChecked620
  · exact pairChecked621
  · exact pairChecked622
  · exact pairChecked623
  · exact pairChecked624
  · exact pairChecked625
  · exact pairChecked626
  · exact pairChecked627
  · exact pairChecked628
  · exact pairChecked629
end RibbonD3WideFinite
