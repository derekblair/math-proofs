import RibbonD3WideJetCheck1
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem jetBlock1 (i : Fin 30) : let z := jetLabel (⟨30+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp z.2.1 z.2.2) (z.1.inp z.2.1 z.2.2) := by
  fin_cases i
  · exact jetChecked30
  · exact jetChecked31
  · exact jetChecked32
  · exact jetChecked33
  · exact jetChecked34
  · exact jetChecked35
  · exact jetChecked36
  · exact jetChecked37
  · exact jetChecked38
  · exact jetChecked39
  · exact jetChecked40
  · exact jetChecked41
  · exact jetChecked42
  · exact jetChecked43
  · exact jetChecked44
  · exact jetChecked45
  · exact jetChecked46
  · exact jetChecked47
  · exact jetChecked48
  · exact jetChecked49
  · exact jetChecked50
  · exact jetChecked51
  · exact jetChecked52
  · exact jetChecked53
  · exact jetChecked54
  · exact jetChecked55
  · exact jetChecked56
  · exact jetChecked57
  · exact jetChecked58
  · exact jetChecked59
end RibbonD3WideFinite
