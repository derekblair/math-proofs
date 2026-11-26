import RibbonD3JetCheck0
import RibbonD3Orbit
namespace RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem jetBlock0 (i : Fin 30) : let z := jetLabel (⟨0+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp z.2.1 z.2.2) (z.1.inp z.2.1 z.2.2) := by
  fin_cases i
  · exact ⟨_,jetChecked0⟩
  · exact ⟨_,jetChecked1⟩
  · exact ⟨_,jetChecked2⟩
  · exact ⟨_,jetChecked3⟩
  · exact ⟨_,jetChecked4⟩
  · exact ⟨_,jetChecked5⟩
  · exact ⟨_,jetChecked6⟩
  · exact ⟨_,jetChecked7⟩
  · exact ⟨_,jetChecked8⟩
  · exact ⟨_,jetChecked9⟩
  · exact ⟨_,jetChecked10⟩
  · exact ⟨_,jetChecked11⟩
  · exact ⟨_,jetChecked12⟩
  · exact ⟨_,jetChecked13⟩
  · exact ⟨_,jetChecked14⟩
  · exact ⟨_,jetChecked15⟩
  · exact ⟨_,jetChecked16⟩
  · exact ⟨_,jetChecked17⟩
  · exact ⟨_,jetChecked18⟩
  · exact ⟨_,jetChecked19⟩
  · exact ⟨_,jetChecked20⟩
  · exact ⟨_,jetChecked21⟩
  · exact ⟨_,jetChecked22⟩
  · exact ⟨_,jetChecked23⟩
  · exact ⟨_,jetChecked24⟩
  · exact ⟨_,jetChecked25⟩
  · exact ⟨_,jetChecked26⟩
  · exact ⟨_,jetChecked27⟩
  · exact ⟨_,jetChecked28⟩
  · exact ⟨_,jetChecked29⟩
end RibbonD3Finite
