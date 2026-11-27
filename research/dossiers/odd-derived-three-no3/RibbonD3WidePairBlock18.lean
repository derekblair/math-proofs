import RibbonD3WidePairCheck18
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock18 (i : Fin 30) : let z := pairLabel (⟨540+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked540
  · exact pairChecked541
  · exact pairChecked542
  · exact pairChecked543
  · exact pairChecked544
  · exact pairChecked545
  · exact pairChecked546
  · exact pairChecked547
  · exact pairChecked548
  · exact pairChecked549
  · exact pairChecked550
  · exact pairChecked551
  · exact pairChecked552
  · exact pairChecked553
  · exact pairChecked554
  · exact pairChecked555
  · exact pairChecked556
  · exact pairChecked557
  · exact pairChecked558
  · exact pairChecked559
  · exact pairChecked560
  · exact pairChecked561
  · exact pairChecked562
  · exact pairChecked563
  · exact pairChecked564
  · exact pairChecked565
  · exact pairChecked566
  · exact pairChecked567
  · exact pairChecked568
  · exact pairChecked569
end RibbonD3WideFinite
