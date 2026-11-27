import RibbonD3WidePairCheck12
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock12 (i : Fin 30) : let z := pairLabel (⟨360+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked360
  · exact pairChecked361
  · exact pairChecked362
  · exact pairChecked363
  · exact pairChecked364
  · exact pairChecked365
  · exact pairChecked366
  · exact pairChecked367
  · exact pairChecked368
  · exact pairChecked369
  · exact pairChecked370
  · exact pairChecked371
  · exact pairChecked372
  · exact pairChecked373
  · exact pairChecked374
  · exact pairChecked375
  · exact pairChecked376
  · exact pairChecked377
  · exact pairChecked378
  · exact pairChecked379
  · exact pairChecked380
  · exact pairChecked381
  · exact pairChecked382
  · exact pairChecked383
  · exact pairChecked384
  · exact pairChecked385
  · exact pairChecked386
  · exact pairChecked387
  · exact pairChecked388
  · exact pairChecked389
end RibbonD3WideFinite
