import NestedAsymBranch
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
namespace NestedExposure
set_option maxHeartbeats 0
set_option maxRecDepth 16000
private theorem row_09_0 : asymFirst 9 0=true := by decide +kernel
private theorem row_09_1 : asymFirst 9 1=true := by decide +kernel
private theorem row_09_2 : asymFirst 9 2=true := by decide +kernel
private theorem row_09_3 : asymFirst 9 3=true := by decide +kernel
private theorem row_09_4 : asymFirst 9 4=true := by decide +kernel
private theorem row_09_5 : asymFirst 9 5=true := by decide +kernel
private theorem row_09_6 : asymFirst 9 6=true := by decide +kernel
private theorem row_09_7 : asymFirst 9 7=true := by decide +kernel
theorem nested_asym_09 : fastScan (asymAccept 9) 9 54 0 Moments.empty=true := by
  apply asym_first_complete
  intro i
  fin_cases i
  · exact row_09_0
  · exact row_09_1
  · exact row_09_2
  · exact row_09_3
  · exact row_09_4
  · exact row_09_5
  · exact row_09_6
  · exact row_09_7
#print axioms nested_asym_09
end NestedExposure
