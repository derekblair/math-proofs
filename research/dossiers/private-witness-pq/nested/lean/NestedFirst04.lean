import NestedAsymBranch
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
namespace NestedExposure
set_option maxHeartbeats 0
set_option maxRecDepth 16000
private theorem row_04_0 : asymFirst 4 0=true := by decide +kernel
private theorem row_04_1 : asymFirst 4 1=true := by decide +kernel
private theorem row_04_2 : asymFirst 4 2=true := by decide +kernel
private theorem row_04_3 : asymFirst 4 3=true := by decide +kernel
private theorem row_04_4 : asymFirst 4 4=true := by decide +kernel
private theorem row_04_5 : asymFirst 4 5=true := by decide +kernel
private theorem row_04_6 : asymFirst 4 6=true := by decide +kernel
private theorem row_04_7 : asymFirst 4 7=true := by decide +kernel
theorem nested_asym_04 : fastScan (asymAccept 4) 9 59 0 Moments.empty=true := by
  apply asym_first_complete
  intro i
  fin_cases i
  · exact row_04_0
  · exact row_04_1
  · exact row_04_2
  · exact row_04_3
  · exact row_04_4
  · exact row_04_5
  · exact row_04_6
  · exact row_04_7
#print axioms nested_asym_04
end NestedExposure
