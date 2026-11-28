import NestedAsymBranch
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
namespace NestedExposure
set_option maxHeartbeats 0
set_option maxRecDepth 16000
private theorem row_12_0 : asymFirst 12 0=true := by decide +kernel
private theorem row_12_1 : asymFirst 12 1=true := by decide +kernel
private theorem row_12_2 : asymFirst 12 2=true := by decide +kernel
private theorem row_12_3 : asymFirst 12 3=true := by decide +kernel
private theorem row_12_4 : asymFirst 12 4=true := by decide +kernel
private theorem row_12_5 : asymFirst 12 5=true := by decide +kernel
private theorem row_12_6 : asymFirst 12 6=true := by decide +kernel
private theorem row_12_7 : asymFirst 12 7=true := by decide +kernel
theorem nested_asym_12 : fastScan (asymAccept 12) 9 51 0 Moments.empty=true := by
  apply asym_first_complete
  intro i
  fin_cases i
  · exact row_12_0
  · exact row_12_1
  · exact row_12_2
  · exact row_12_3
  · exact row_12_4
  · exact row_12_5
  · exact row_12_6
  · exact row_12_7
#print axioms nested_asym_12
end NestedExposure
