import NestedAsymBranch
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
namespace NestedExposure
set_option maxHeartbeats 0
set_option maxRecDepth 16000
private theorem row_02_0 : asymFirst 2 0=true := by decide +kernel
private theorem row_02_1 : asymFirst 2 1=true := by decide +kernel
private theorem row_02_2 : asymFirst 2 2=true := by decide +kernel
private theorem row_02_3 : asymFirst 2 3=true := by decide +kernel
private theorem row_02_4 : asymFirst 2 4=true := by decide +kernel
private theorem row_02_5 : asymFirst 2 5=true := by decide +kernel
private theorem row_02_6 : asymFirst 2 6=true := by decide +kernel
private theorem row_02_7 : asymFirst 2 7=true := by decide +kernel
theorem nested_asym_02 : fastScan (asymAccept 2) 9 61 0 Moments.empty=true := by
  apply asym_first_complete
  intro i
  fin_cases i
  · exact row_02_0
  · exact row_02_1
  · exact row_02_2
  · exact row_02_3
  · exact row_02_4
  · exact row_02_5
  · exact row_02_6
  · exact row_02_7
#print axioms nested_asym_02
end NestedExposure
