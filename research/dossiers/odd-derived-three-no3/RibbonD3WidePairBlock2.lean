import RibbonD3WidePairCheck2
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock2 (i : Fin 30) : let z := pairLabel (⟨60+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked60
  · exact pairChecked61
  · exact pairChecked62
  · exact pairChecked63
  · exact pairChecked64
  · exact pairChecked65
  · exact pairChecked66
  · exact pairChecked67
  · exact pairChecked68
  · exact pairChecked69
  · exact pairChecked70
  · exact pairChecked71
  · exact pairChecked72
  · exact pairChecked73
  · exact pairChecked74
  · exact pairChecked75
  · exact pairChecked76
  · exact pairChecked77
  · exact pairChecked78
  · exact pairChecked79
  · exact pairChecked80
  · exact pairChecked81
  · exact pairChecked82
  · exact pairChecked83
  · exact pairChecked84
  · exact pairChecked85
  · exact pairChecked86
  · exact pairChecked87
  · exact pairChecked88
  · exact pairChecked89
end RibbonD3WideFinite
