import NestedAsymBranch
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
namespace NestedExposure
set_option maxHeartbeats 0
set_option maxRecDepth 16000
private theorem row_01_0 : asymFirst 1 0=true := by decide +kernel
private theorem row_01_1 : asymFirst 1 1=true := by decide +kernel
private theorem row_01_2 : asymFirst 1 2=true := by decide +kernel
private theorem row_01_3 : asymFirst 1 3=true := by decide +kernel
private theorem row_01_4 : asymFirst 1 4=true := by decide +kernel
private theorem row_01_5 : asymFirst 1 5=true := by decide +kernel
private theorem row_01_6 : asymFirst 1 6=true := by decide +kernel
private theorem row_01_7 : asymFirst 1 7=true := by decide +kernel
theorem nested_asym_01 : fastScan (asymAccept 1) 9 62 0 Moments.empty=true := by
  apply asym_first_complete
  intro i
  fin_cases i
  · exact row_01_0
  · exact row_01_1
  · exact row_01_2
  · exact row_01_3
  · exact row_01_4
  · exact row_01_5
  · exact row_01_6
  · exact row_01_7
#print axioms nested_asym_01
end NestedExposure
