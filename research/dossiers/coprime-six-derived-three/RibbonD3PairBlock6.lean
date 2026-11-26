import RibbonD3PairCheck6
import RibbonD3Orbit
namespace RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock6 (i : Fin 30) : let z := pairLabel (⟨180+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact ⟨_,pairChecked180⟩
  · exact ⟨_,pairChecked181⟩
  · exact ⟨_,pairChecked182⟩
  · exact ⟨_,pairChecked183⟩
  · exact ⟨_,pairChecked184⟩
  · exact ⟨_,pairChecked185⟩
  · exact ⟨_,pairChecked186⟩
  · exact ⟨_,pairChecked187⟩
  · exact ⟨_,pairChecked188⟩
  · exact ⟨_,pairChecked189⟩
  · exact ⟨_,pairChecked190⟩
  · exact ⟨_,pairChecked191⟩
  · exact ⟨_,pairChecked192⟩
  · exact ⟨_,pairChecked193⟩
  · exact ⟨_,pairChecked194⟩
  · exact ⟨_,pairChecked195⟩
  · exact ⟨_,pairChecked196⟩
  · exact ⟨_,pairChecked197⟩
  · exact ⟨_,pairChecked198⟩
  · exact ⟨_,pairChecked199⟩
  · exact ⟨_,pairChecked200⟩
  · exact ⟨_,pairChecked201⟩
  · exact ⟨_,pairChecked202⟩
  · exact ⟨_,pairChecked203⟩
  · exact ⟨_,pairChecked204⟩
  · exact ⟨_,pairChecked205⟩
  · exact ⟨_,pairChecked206⟩
  · exact ⟨_,pairChecked207⟩
  · exact ⟨_,pairChecked208⟩
  · exact ⟨_,pairChecked209⟩
end RibbonD3Finite
