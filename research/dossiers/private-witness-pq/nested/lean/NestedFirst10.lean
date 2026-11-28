import NestedAsymBranch
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
namespace NestedExposure
set_option maxHeartbeats 0
set_option maxRecDepth 16000
private theorem row_10_0 : asymFirst 10 0=true := by decide +kernel
private theorem row_10_1 : asymFirst 10 1=true := by decide +kernel
private theorem row_10_2 : asymFirst 10 2=true := by decide +kernel
private theorem row_10_3 : asymFirst 10 3=true := by decide +kernel
private theorem row_10_4 : asymFirst 10 4=true := by decide +kernel
private theorem row_10_5 : asymFirst 10 5=true := by decide +kernel
private theorem row_10_6 : asymFirst 10 6=true := by decide +kernel
private theorem row_10_7 : asymFirst 10 7=true := by decide +kernel
theorem nested_asym_10 : fastScan (asymAccept 10) 9 53 0 Moments.empty=true := by
  apply asym_first_complete
  intro i
  fin_cases i
  · exact row_10_0
  · exact row_10_1
  · exact row_10_2
  · exact row_10_3
  · exact row_10_4
  · exact row_10_5
  · exact row_10_6
  · exact row_10_7
#print axioms nested_asym_10
end NestedExposure
