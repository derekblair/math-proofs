import RibbonD3WidePairCheck10
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock10 (i : Fin 30) : let z := pairLabel (⟨300+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked300
  · exact pairChecked301
  · exact pairChecked302
  · exact pairChecked303
  · exact pairChecked304
  · exact pairChecked305
  · exact pairChecked306
  · exact pairChecked307
  · exact pairChecked308
  · exact pairChecked309
  · exact pairChecked310
  · exact pairChecked311
  · exact pairChecked312
  · exact pairChecked313
  · exact pairChecked314
  · exact pairChecked315
  · exact pairChecked316
  · exact pairChecked317
  · exact pairChecked318
  · exact pairChecked319
  · exact pairChecked320
  · exact pairChecked321
  · exact pairChecked322
  · exact pairChecked323
  · exact pairChecked324
  · exact pairChecked325
  · exact pairChecked326
  · exact pairChecked327
  · exact pairChecked328
  · exact pairChecked329
end RibbonD3WideFinite
