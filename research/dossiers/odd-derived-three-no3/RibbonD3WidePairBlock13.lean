import RibbonD3WidePairCheck13
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock13 (i : Fin 30) : let z := pairLabel (⟨390+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked390
  · exact pairChecked391
  · exact pairChecked392
  · exact pairChecked393
  · exact pairChecked394
  · exact pairChecked395
  · exact pairChecked396
  · exact pairChecked397
  · exact pairChecked398
  · exact pairChecked399
  · exact pairChecked400
  · exact pairChecked401
  · exact pairChecked402
  · exact pairChecked403
  · exact pairChecked404
  · exact pairChecked405
  · exact pairChecked406
  · exact pairChecked407
  · exact pairChecked408
  · exact pairChecked409
  · exact pairChecked410
  · exact pairChecked411
  · exact pairChecked412
  · exact pairChecked413
  · exact pairChecked414
  · exact pairChecked415
  · exact pairChecked416
  · exact pairChecked417
  · exact pairChecked418
  · exact pairChecked419
end RibbonD3WideFinite
