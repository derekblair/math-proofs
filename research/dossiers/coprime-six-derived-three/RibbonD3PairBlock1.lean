import RibbonD3PairCheck1
import RibbonD3Orbit
namespace RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock1 (i : Fin 30) : let z := pairLabel (⟨30+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact ⟨_,pairChecked30⟩
  · exact ⟨_,pairChecked31⟩
  · exact ⟨_,pairChecked32⟩
  · exact ⟨_,pairChecked33⟩
  · exact ⟨_,pairChecked34⟩
  · exact ⟨_,pairChecked35⟩
  · exact ⟨_,pairChecked36⟩
  · exact ⟨_,pairChecked37⟩
  · exact ⟨_,pairChecked38⟩
  · exact ⟨_,pairChecked39⟩
  · exact ⟨_,pairChecked40⟩
  · exact ⟨_,pairChecked41⟩
  · exact ⟨_,pairChecked42⟩
  · exact ⟨_,pairChecked43⟩
  · exact ⟨_,pairChecked44⟩
  · exact ⟨_,pairChecked45⟩
  · exact ⟨_,pairChecked46⟩
  · exact ⟨_,pairChecked47⟩
  · exact ⟨_,pairChecked48⟩
  · exact ⟨_,pairChecked49⟩
  · exact ⟨_,pairChecked50⟩
  · exact ⟨_,pairChecked51⟩
  · exact ⟨_,pairChecked52⟩
  · exact ⟨_,pairChecked53⟩
  · exact ⟨_,pairChecked54⟩
  · exact ⟨_,pairChecked55⟩
  · exact ⟨_,pairChecked56⟩
  · exact ⟨_,pairChecked57⟩
  · exact ⟨_,pairChecked58⟩
  · exact ⟨_,pairChecked59⟩
end RibbonD3Finite
