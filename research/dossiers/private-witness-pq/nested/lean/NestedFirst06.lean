import NestedAsymBranch
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
namespace NestedExposure
set_option maxHeartbeats 0
set_option maxRecDepth 16000
private theorem row_06_0 : asymFirst 6 0=true := by decide +kernel
private theorem row_06_1 : asymFirst 6 1=true := by decide +kernel
private theorem row_06_2 : asymFirst 6 2=true := by decide +kernel
private theorem row_06_3 : asymFirst 6 3=true := by decide +kernel
private theorem row_06_4 : asymFirst 6 4=true := by decide +kernel
private theorem row_06_5 : asymFirst 6 5=true := by decide +kernel
private theorem row_06_6 : asymFirst 6 6=true := by decide +kernel
private theorem row_06_7 : asymFirst 6 7=true := by decide +kernel
theorem nested_asym_06 : fastScan (asymAccept 6) 9 57 0 Moments.empty=true := by
  apply asym_first_complete
  intro i
  fin_cases i
  · exact row_06_0
  · exact row_06_1
  · exact row_06_2
  · exact row_06_3
  · exact row_06_4
  · exact row_06_5
  · exact row_06_6
  · exact row_06_7
#print axioms nested_asym_06
end NestedExposure
