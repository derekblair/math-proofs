import RibbonD3WidePairCheck1
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock1 (i : Fin 30) : let z := pairLabel (⟨30+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked30
  · exact pairChecked31
  · exact pairChecked32
  · exact pairChecked33
  · exact pairChecked34
  · exact pairChecked35
  · exact pairChecked36
  · exact pairChecked37
  · exact pairChecked38
  · exact pairChecked39
  · exact pairChecked40
  · exact pairChecked41
  · exact pairChecked42
  · exact pairChecked43
  · exact pairChecked44
  · exact pairChecked45
  · exact pairChecked46
  · exact pairChecked47
  · exact pairChecked48
  · exact pairChecked49
  · exact pairChecked50
  · exact pairChecked51
  · exact pairChecked52
  · exact pairChecked53
  · exact pairChecked54
  · exact pairChecked55
  · exact pairChecked56
  · exact pairChecked57
  · exact pairChecked58
  · exact pairChecked59
end RibbonD3WideFinite
