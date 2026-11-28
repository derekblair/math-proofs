import NestedAsymBranch
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
namespace NestedExposure
set_option maxHeartbeats 0
set_option maxRecDepth 16000
private theorem row_07_0 : asymFirst 7 0=true := by decide +kernel
private theorem row_07_1 : asymFirst 7 1=true := by decide +kernel
private theorem row_07_2 : asymFirst 7 2=true := by decide +kernel
private theorem row_07_3 : asymFirst 7 3=true := by decide +kernel
private theorem row_07_4 : asymFirst 7 4=true := by decide +kernel
private theorem row_07_5 : asymFirst 7 5=true := by decide +kernel
private theorem row_07_6 : asymFirst 7 6=true := by decide +kernel
private theorem row_07_7 : asymFirst 7 7=true := by decide +kernel
theorem nested_asym_07 : fastScan (asymAccept 7) 9 56 0 Moments.empty=true := by
  apply asym_first_complete
  intro i
  fin_cases i
  · exact row_07_0
  · exact row_07_1
  · exact row_07_2
  · exact row_07_3
  · exact row_07_4
  · exact row_07_5
  · exact row_07_6
  · exact row_07_7
#print axioms nested_asym_07
end NestedExposure
