import NestedAsymBranch
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
namespace NestedExposure
set_option maxHeartbeats 0
set_option maxRecDepth 16000
private theorem row_13_0 : asymFirst 13 0=true := by decide +kernel
private theorem row_13_1 : asymFirst 13 1=true := by decide +kernel
private theorem row_13_2 : asymFirst 13 2=true := by decide +kernel
private theorem row_13_3 : asymFirst 13 3=true := by decide +kernel
private theorem row_13_4 : asymFirst 13 4=true := by decide +kernel
private theorem row_13_5 : asymFirst 13 5=true := by decide +kernel
private theorem row_13_6 : asymFirst 13 6=true := by decide +kernel
private theorem row_13_7 : asymFirst 13 7=true := by decide +kernel
theorem nested_asym_13 : fastScan (asymAccept 13) 9 50 0 Moments.empty=true := by
  apply asym_first_complete
  intro i
  fin_cases i
  · exact row_13_0
  · exact row_13_1
  · exact row_13_2
  · exact row_13_3
  · exact row_13_4
  · exact row_13_5
  · exact row_13_6
  · exact row_13_7
#print axioms nested_asym_13
end NestedExposure
