import RibbonD3WidePairCheck11
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock11 (i : Fin 30) : let z := pairLabel (⟨330+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked330
  · exact pairChecked331
  · exact pairChecked332
  · exact pairChecked333
  · exact pairChecked334
  · exact pairChecked335
  · exact pairChecked336
  · exact pairChecked337
  · exact pairChecked338
  · exact pairChecked339
  · exact pairChecked340
  · exact pairChecked341
  · exact pairChecked342
  · exact pairChecked343
  · exact pairChecked344
  · exact pairChecked345
  · exact pairChecked346
  · exact pairChecked347
  · exact pairChecked348
  · exact pairChecked349
  · exact pairChecked350
  · exact pairChecked351
  · exact pairChecked352
  · exact pairChecked353
  · exact pairChecked354
  · exact pairChecked355
  · exact pairChecked356
  · exact pairChecked357
  · exact pairChecked358
  · exact pairChecked359
end RibbonD3WideFinite
