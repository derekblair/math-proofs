import RibbonD3PairCheck7
import RibbonD3Orbit
namespace RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock7 (i : Fin 3) : let z := pairLabel (⟨210+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact ⟨_,pairChecked210⟩
  · exact ⟨_,pairChecked211⟩
  · exact ⟨_,pairChecked212⟩
end RibbonD3Finite
