import NestedAsymBranch
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
namespace NestedExposure
set_option maxHeartbeats 0
set_option maxRecDepth 16000
private theorem row_05_0 : asymFirst 5 0=true := by decide +kernel
private theorem row_05_1 : asymFirst 5 1=true := by decide +kernel
private theorem row_05_2 : asymFirst 5 2=true := by decide +kernel
private theorem row_05_3 : asymFirst 5 3=true := by decide +kernel
private theorem row_05_4 : asymFirst 5 4=true := by decide +kernel
private theorem row_05_5 : asymFirst 5 5=true := by decide +kernel
private theorem row_05_6 : asymFirst 5 6=true := by decide +kernel
private theorem row_05_7 : asymFirst 5 7=true := by decide +kernel
theorem nested_asym_05 : fastScan (asymAccept 5) 9 58 0 Moments.empty=true := by
  apply asym_first_complete
  intro i
  fin_cases i
  · exact row_05_0
  · exact row_05_1
  · exact row_05_2
  · exact row_05_3
  · exact row_05_4
  · exact row_05_5
  · exact row_05_6
  · exact row_05_7
#print axioms nested_asym_05
end NestedExposure
