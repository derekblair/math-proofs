import RibbonD3WidePairCheck17
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock17 (i : Fin 30) : let z := pairLabel (⟨510+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked510
  · exact pairChecked511
  · exact pairChecked512
  · exact pairChecked513
  · exact pairChecked514
  · exact pairChecked515
  · exact pairChecked516
  · exact pairChecked517
  · exact pairChecked518
  · exact pairChecked519
  · exact pairChecked520
  · exact pairChecked521
  · exact pairChecked522
  · exact pairChecked523
  · exact pairChecked524
  · exact pairChecked525
  · exact pairChecked526
  · exact pairChecked527
  · exact pairChecked528
  · exact pairChecked529
  · exact pairChecked530
  · exact pairChecked531
  · exact pairChecked532
  · exact pairChecked533
  · exact pairChecked534
  · exact pairChecked535
  · exact pairChecked536
  · exact pairChecked537
  · exact pairChecked538
  · exact pairChecked539
end RibbonD3WideFinite
