import RibbonD3WidePairCheck14
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock14 (i : Fin 30) : let z := pairLabel (⟨420+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked420
  · exact pairChecked421
  · exact pairChecked422
  · exact pairChecked423
  · exact pairChecked424
  · exact pairChecked425
  · exact pairChecked426
  · exact pairChecked427
  · exact pairChecked428
  · exact pairChecked429
  · exact pairChecked430
  · exact pairChecked431
  · exact pairChecked432
  · exact pairChecked433
  · exact pairChecked434
  · exact pairChecked435
  · exact pairChecked436
  · exact pairChecked437
  · exact pairChecked438
  · exact pairChecked439
  · exact pairChecked440
  · exact pairChecked441
  · exact pairChecked442
  · exact pairChecked443
  · exact pairChecked444
  · exact pairChecked445
  · exact pairChecked446
  · exact pairChecked447
  · exact pairChecked448
  · exact pairChecked449
end RibbonD3WideFinite
