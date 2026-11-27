import RibbonD3WideJetCheck2
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem jetBlock2 (i : Fin 30) : let z := jetLabel (⟨60+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp z.2.1 z.2.2) (z.1.inp z.2.1 z.2.2) := by
  fin_cases i
  · exact jetChecked60
  · exact jetChecked61
  · exact jetChecked62
  · exact jetChecked63
  · exact jetChecked64
  · exact jetChecked65
  · exact jetChecked66
  · exact jetChecked67
  · exact jetChecked68
  · exact jetChecked69
  · exact jetChecked70
  · exact jetChecked71
  · exact jetChecked72
  · exact jetChecked73
  · exact jetChecked74
  · exact jetChecked75
  · exact jetChecked76
  · exact jetChecked77
  · exact jetChecked78
  · exact jetChecked79
  · exact jetChecked80
  · exact jetChecked81
  · exact jetChecked82
  · exact jetChecked83
  · exact jetChecked84
  · exact jetChecked85
  · exact jetChecked86
  · exact jetChecked87
  · exact jetChecked88
  · exact jetChecked89
end RibbonD3WideFinite
