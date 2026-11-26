import RibbonD3PairCheck4
import RibbonD3Orbit
namespace RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock4 (i : Fin 30) : let z := pairLabel (⟨120+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact ⟨_,pairChecked120⟩
  · exact ⟨_,pairChecked121⟩
  · exact ⟨_,pairChecked122⟩
  · exact ⟨_,pairChecked123⟩
  · exact ⟨_,pairChecked124⟩
  · exact ⟨_,pairChecked125⟩
  · exact ⟨_,pairChecked126⟩
  · exact ⟨_,pairChecked127⟩
  · exact ⟨_,pairChecked128⟩
  · exact ⟨_,pairChecked129⟩
  · exact ⟨_,pairChecked130⟩
  · exact ⟨_,pairChecked131⟩
  · exact ⟨_,pairChecked132⟩
  · exact ⟨_,pairChecked133⟩
  · exact ⟨_,pairChecked134⟩
  · exact ⟨_,pairChecked135⟩
  · exact ⟨_,pairChecked136⟩
  · exact ⟨_,pairChecked137⟩
  · exact ⟨_,pairChecked138⟩
  · exact ⟨_,pairChecked139⟩
  · exact ⟨_,pairChecked140⟩
  · exact ⟨_,pairChecked141⟩
  · exact ⟨_,pairChecked142⟩
  · exact ⟨_,pairChecked143⟩
  · exact ⟨_,pairChecked144⟩
  · exact ⟨_,pairChecked145⟩
  · exact ⟨_,pairChecked146⟩
  · exact ⟨_,pairChecked147⟩
  · exact ⟨_,pairChecked148⟩
  · exact ⟨_,pairChecked149⟩
end RibbonD3Finite
