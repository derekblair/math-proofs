import RibbonD3PairCheck2
import RibbonD3Orbit
namespace RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock2 (i : Fin 30) : let z := pairLabel (⟨60+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact ⟨_,pairChecked60⟩
  · exact ⟨_,pairChecked61⟩
  · exact ⟨_,pairChecked62⟩
  · exact ⟨_,pairChecked63⟩
  · exact ⟨_,pairChecked64⟩
  · exact ⟨_,pairChecked65⟩
  · exact ⟨_,pairChecked66⟩
  · exact ⟨_,pairChecked67⟩
  · exact ⟨_,pairChecked68⟩
  · exact ⟨_,pairChecked69⟩
  · exact ⟨_,pairChecked70⟩
  · exact ⟨_,pairChecked71⟩
  · exact ⟨_,pairChecked72⟩
  · exact ⟨_,pairChecked73⟩
  · exact ⟨_,pairChecked74⟩
  · exact ⟨_,pairChecked75⟩
  · exact ⟨_,pairChecked76⟩
  · exact ⟨_,pairChecked77⟩
  · exact ⟨_,pairChecked78⟩
  · exact ⟨_,pairChecked79⟩
  · exact ⟨_,pairChecked80⟩
  · exact ⟨_,pairChecked81⟩
  · exact ⟨_,pairChecked82⟩
  · exact ⟨_,pairChecked83⟩
  · exact ⟨_,pairChecked84⟩
  · exact ⟨_,pairChecked85⟩
  · exact ⟨_,pairChecked86⟩
  · exact ⟨_,pairChecked87⟩
  · exact ⟨_,pairChecked88⟩
  · exact ⟨_,pairChecked89⟩
end RibbonD3Finite
