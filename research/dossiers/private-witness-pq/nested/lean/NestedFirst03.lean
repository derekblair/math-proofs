import NestedAsymBranch
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
namespace NestedExposure
set_option maxHeartbeats 0
set_option maxRecDepth 16000
private theorem row_03_0 : asymFirst 3 0=true := by decide +kernel
private theorem row_03_1 : asymFirst 3 1=true := by decide +kernel
private theorem row_03_2 : asymFirst 3 2=true := by decide +kernel
private theorem row_03_3 : asymFirst 3 3=true := by decide +kernel
private theorem row_03_4 : asymFirst 3 4=true := by decide +kernel
private theorem row_03_5 : asymFirst 3 5=true := by decide +kernel
private theorem row_03_6 : asymFirst 3 6=true := by decide +kernel
private theorem row_03_7 : asymFirst 3 7=true := by decide +kernel
theorem nested_asym_03 : fastScan (asymAccept 3) 9 60 0 Moments.empty=true := by
  apply asym_first_complete
  intro i
  fin_cases i
  · exact row_03_0
  · exact row_03_1
  · exact row_03_2
  · exact row_03_3
  · exact row_03_4
  · exact row_03_5
  · exact row_03_6
  · exact row_03_7
#print axioms nested_asym_03
end NestedExposure
