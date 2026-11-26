import RibbonD3JetCheck4
import RibbonD3Orbit
namespace RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem jetBlock4 (i : Fin 17) : let z := jetLabel (⟨120+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp z.2.1 z.2.2) (z.1.inp z.2.1 z.2.2) := by
  fin_cases i
  · exact ⟨_,jetChecked120⟩
  · exact ⟨_,jetChecked121⟩
  · exact ⟨_,jetChecked122⟩
  · exact ⟨_,jetChecked123⟩
  · exact ⟨_,jetChecked124⟩
  · exact ⟨_,jetChecked125⟩
  · exact ⟨_,jetChecked126⟩
  · exact ⟨_,jetChecked127⟩
  · exact ⟨_,jetChecked128⟩
  · exact ⟨_,jetChecked129⟩
  · exact ⟨_,jetChecked130⟩
  · exact ⟨_,jetChecked131⟩
  · exact ⟨_,jetChecked132⟩
  · exact ⟨_,jetChecked133⟩
  · exact ⟨_,jetChecked134⟩
  · exact ⟨_,jetChecked135⟩
  · exact ⟨_,jetChecked136⟩
end RibbonD3Finite
