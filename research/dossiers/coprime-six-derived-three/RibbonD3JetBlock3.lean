import RibbonD3JetCheck3
import RibbonD3Orbit
namespace RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem jetBlock3 (i : Fin 30) : let z := jetLabel (⟨90+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp z.2.1 z.2.2) (z.1.inp z.2.1 z.2.2) := by
  fin_cases i
  · exact ⟨_,jetChecked90⟩
  · exact ⟨_,jetChecked91⟩
  · exact ⟨_,jetChecked92⟩
  · exact ⟨_,jetChecked93⟩
  · exact ⟨_,jetChecked94⟩
  · exact ⟨_,jetChecked95⟩
  · exact ⟨_,jetChecked96⟩
  · exact ⟨_,jetChecked97⟩
  · exact ⟨_,jetChecked98⟩
  · exact ⟨_,jetChecked99⟩
  · exact ⟨_,jetChecked100⟩
  · exact ⟨_,jetChecked101⟩
  · exact ⟨_,jetChecked102⟩
  · exact ⟨_,jetChecked103⟩
  · exact ⟨_,jetChecked104⟩
  · exact ⟨_,jetChecked105⟩
  · exact ⟨_,jetChecked106⟩
  · exact ⟨_,jetChecked107⟩
  · exact ⟨_,jetChecked108⟩
  · exact ⟨_,jetChecked109⟩
  · exact ⟨_,jetChecked110⟩
  · exact ⟨_,jetChecked111⟩
  · exact ⟨_,jetChecked112⟩
  · exact ⟨_,jetChecked113⟩
  · exact ⟨_,jetChecked114⟩
  · exact ⟨_,jetChecked115⟩
  · exact ⟨_,jetChecked116⟩
  · exact ⟨_,jetChecked117⟩
  · exact ⟨_,jetChecked118⟩
  · exact ⟨_,jetChecked119⟩
end RibbonD3Finite
