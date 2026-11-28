import NestedAsymBranch
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
namespace NestedExposure
set_option maxHeartbeats 0
set_option maxRecDepth 16000
private theorem row_08_0 : asymFirst 8 0=true := by decide +kernel
private theorem row_08_1 : asymFirst 8 1=true := by decide +kernel
private theorem row_08_2 : asymFirst 8 2=true := by decide +kernel
private theorem row_08_3 : asymFirst 8 3=true := by decide +kernel
private theorem row_08_4 : asymFirst 8 4=true := by decide +kernel
private theorem row_08_5 : asymFirst 8 5=true := by decide +kernel
private theorem row_08_6 : asymFirst 8 6=true := by decide +kernel
private theorem row_08_7 : asymFirst 8 7=true := by decide +kernel
theorem nested_asym_08 : fastScan (asymAccept 8) 9 55 0 Moments.empty=true := by
  apply asym_first_complete
  intro i
  fin_cases i
  · exact row_08_0
  · exact row_08_1
  · exact row_08_2
  · exact row_08_3
  · exact row_08_4
  · exact row_08_5
  · exact row_08_6
  · exact row_08_7
#print axioms nested_asym_08
end NestedExposure
