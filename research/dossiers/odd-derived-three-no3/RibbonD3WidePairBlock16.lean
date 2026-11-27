import RibbonD3WidePairCheck16
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock16 (i : Fin 30) : let z := pairLabel (⟨480+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked480
  · exact pairChecked481
  · exact pairChecked482
  · exact pairChecked483
  · exact pairChecked484
  · exact pairChecked485
  · exact pairChecked486
  · exact pairChecked487
  · exact pairChecked488
  · exact pairChecked489
  · exact pairChecked490
  · exact pairChecked491
  · exact pairChecked492
  · exact pairChecked493
  · exact pairChecked494
  · exact pairChecked495
  · exact pairChecked496
  · exact pairChecked497
  · exact pairChecked498
  · exact pairChecked499
  · exact pairChecked500
  · exact pairChecked501
  · exact pairChecked502
  · exact pairChecked503
  · exact pairChecked504
  · exact pairChecked505
  · exact pairChecked506
  · exact pairChecked507
  · exact pairChecked508
  · exact pairChecked509
end RibbonD3WideFinite
