import RibbonD3JetCheck1
import RibbonD3Orbit
namespace RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem jetBlock1 (i : Fin 30) : let z := jetLabel (⟨30+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp z.2.1 z.2.2) (z.1.inp z.2.1 z.2.2) := by
  fin_cases i
  · exact ⟨_,jetChecked30⟩
  · exact ⟨_,jetChecked31⟩
  · exact ⟨_,jetChecked32⟩
  · exact ⟨_,jetChecked33⟩
  · exact ⟨_,jetChecked34⟩
  · exact ⟨_,jetChecked35⟩
  · exact ⟨_,jetChecked36⟩
  · exact ⟨_,jetChecked37⟩
  · exact ⟨_,jetChecked38⟩
  · exact ⟨_,jetChecked39⟩
  · exact ⟨_,jetChecked40⟩
  · exact ⟨_,jetChecked41⟩
  · exact ⟨_,jetChecked42⟩
  · exact ⟨_,jetChecked43⟩
  · exact ⟨_,jetChecked44⟩
  · exact ⟨_,jetChecked45⟩
  · exact ⟨_,jetChecked46⟩
  · exact ⟨_,jetChecked47⟩
  · exact ⟨_,jetChecked48⟩
  · exact ⟨_,jetChecked49⟩
  · exact ⟨_,jetChecked50⟩
  · exact ⟨_,jetChecked51⟩
  · exact ⟨_,jetChecked52⟩
  · exact ⟨_,jetChecked53⟩
  · exact ⟨_,jetChecked54⟩
  · exact ⟨_,jetChecked55⟩
  · exact ⟨_,jetChecked56⟩
  · exact ⟨_,jetChecked57⟩
  · exact ⟨_,jetChecked58⟩
  · exact ⟨_,jetChecked59⟩
end RibbonD3Finite
