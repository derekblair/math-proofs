import RibbonD3JetCheck2
import RibbonD3Orbit
namespace RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem jetBlock2 (i : Fin 30) : let z := jetLabel (⟨60+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp z.2.1 z.2.2) (z.1.inp z.2.1 z.2.2) := by
  fin_cases i
  · exact ⟨_,jetChecked60⟩
  · exact ⟨_,jetChecked61⟩
  · exact ⟨_,jetChecked62⟩
  · exact ⟨_,jetChecked63⟩
  · exact ⟨_,jetChecked64⟩
  · exact ⟨_,jetChecked65⟩
  · exact ⟨_,jetChecked66⟩
  · exact ⟨_,jetChecked67⟩
  · exact ⟨_,jetChecked68⟩
  · exact ⟨_,jetChecked69⟩
  · exact ⟨_,jetChecked70⟩
  · exact ⟨_,jetChecked71⟩
  · exact ⟨_,jetChecked72⟩
  · exact ⟨_,jetChecked73⟩
  · exact ⟨_,jetChecked74⟩
  · exact ⟨_,jetChecked75⟩
  · exact ⟨_,jetChecked76⟩
  · exact ⟨_,jetChecked77⟩
  · exact ⟨_,jetChecked78⟩
  · exact ⟨_,jetChecked79⟩
  · exact ⟨_,jetChecked80⟩
  · exact ⟨_,jetChecked81⟩
  · exact ⟨_,jetChecked82⟩
  · exact ⟨_,jetChecked83⟩
  · exact ⟨_,jetChecked84⟩
  · exact ⟨_,jetChecked85⟩
  · exact ⟨_,jetChecked86⟩
  · exact ⟨_,jetChecked87⟩
  · exact ⟨_,jetChecked88⟩
  · exact ⟨_,jetChecked89⟩
end RibbonD3Finite
