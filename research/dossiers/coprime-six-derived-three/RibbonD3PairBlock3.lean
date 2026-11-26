import RibbonD3PairCheck3
import RibbonD3Orbit
namespace RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock3 (i : Fin 30) : let z := pairLabel (⟨90+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact ⟨_,pairChecked90⟩
  · exact ⟨_,pairChecked91⟩
  · exact ⟨_,pairChecked92⟩
  · exact ⟨_,pairChecked93⟩
  · exact ⟨_,pairChecked94⟩
  · exact ⟨_,pairChecked95⟩
  · exact ⟨_,pairChecked96⟩
  · exact ⟨_,pairChecked97⟩
  · exact ⟨_,pairChecked98⟩
  · exact ⟨_,pairChecked99⟩
  · exact ⟨_,pairChecked100⟩
  · exact ⟨_,pairChecked101⟩
  · exact ⟨_,pairChecked102⟩
  · exact ⟨_,pairChecked103⟩
  · exact ⟨_,pairChecked104⟩
  · exact ⟨_,pairChecked105⟩
  · exact ⟨_,pairChecked106⟩
  · exact ⟨_,pairChecked107⟩
  · exact ⟨_,pairChecked108⟩
  · exact ⟨_,pairChecked109⟩
  · exact ⟨_,pairChecked110⟩
  · exact ⟨_,pairChecked111⟩
  · exact ⟨_,pairChecked112⟩
  · exact ⟨_,pairChecked113⟩
  · exact ⟨_,pairChecked114⟩
  · exact ⟨_,pairChecked115⟩
  · exact ⟨_,pairChecked116⟩
  · exact ⟨_,pairChecked117⟩
  · exact ⟨_,pairChecked118⟩
  · exact ⟨_,pairChecked119⟩
end RibbonD3Finite
