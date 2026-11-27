import RibbonD3WidePairCheck15
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock15 (i : Fin 30) : let z := pairLabel (⟨450+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked450
  · exact pairChecked451
  · exact pairChecked452
  · exact pairChecked453
  · exact pairChecked454
  · exact pairChecked455
  · exact pairChecked456
  · exact pairChecked457
  · exact pairChecked458
  · exact pairChecked459
  · exact pairChecked460
  · exact pairChecked461
  · exact pairChecked462
  · exact pairChecked463
  · exact pairChecked464
  · exact pairChecked465
  · exact pairChecked466
  · exact pairChecked467
  · exact pairChecked468
  · exact pairChecked469
  · exact pairChecked470
  · exact pairChecked471
  · exact pairChecked472
  · exact pairChecked473
  · exact pairChecked474
  · exact pairChecked475
  · exact pairChecked476
  · exact pairChecked477
  · exact pairChecked478
  · exact pairChecked479
end RibbonD3WideFinite
