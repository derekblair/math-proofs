import RibbonD3PairCheck0
import RibbonD3Orbit
namespace RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock0 (i : Fin 30) : let z := pairLabel (⟨0+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact ⟨_,pairChecked0⟩
  · exact ⟨_,pairChecked1⟩
  · exact ⟨_,pairChecked2⟩
  · exact ⟨_,pairChecked3⟩
  · exact ⟨_,pairChecked4⟩
  · exact ⟨_,pairChecked5⟩
  · exact ⟨_,pairChecked6⟩
  · exact ⟨_,pairChecked7⟩
  · exact ⟨_,pairChecked8⟩
  · exact ⟨_,pairChecked9⟩
  · exact ⟨_,pairChecked10⟩
  · exact ⟨_,pairChecked11⟩
  · exact ⟨_,pairChecked12⟩
  · exact ⟨_,pairChecked13⟩
  · exact ⟨_,pairChecked14⟩
  · exact ⟨_,pairChecked15⟩
  · exact ⟨_,pairChecked16⟩
  · exact ⟨_,pairChecked17⟩
  · exact ⟨_,pairChecked18⟩
  · exact ⟨_,pairChecked19⟩
  · exact ⟨_,pairChecked20⟩
  · exact ⟨_,pairChecked21⟩
  · exact ⟨_,pairChecked22⟩
  · exact ⟨_,pairChecked23⟩
  · exact ⟨_,pairChecked24⟩
  · exact ⟨_,pairChecked25⟩
  · exact ⟨_,pairChecked26⟩
  · exact ⟨_,pairChecked27⟩
  · exact ⟨_,pairChecked28⟩
  · exact ⟨_,pairChecked29⟩
end RibbonD3Finite
