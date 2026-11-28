import NestedAsymBranch
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
namespace NestedExposure
set_option maxHeartbeats 0
set_option maxRecDepth 16000
private theorem row_11_0 : asymFirst 11 0=true := by decide +kernel
private theorem row_11_1 : asymFirst 11 1=true := by decide +kernel
private theorem row_11_2 : asymFirst 11 2=true := by decide +kernel
private theorem row_11_3 : asymFirst 11 3=true := by decide +kernel
private theorem row_11_4 : asymFirst 11 4=true := by decide +kernel
private theorem row_11_5 : asymFirst 11 5=true := by decide +kernel
private theorem row_11_6 : asymFirst 11 6=true := by decide +kernel
private theorem row_11_7 : asymFirst 11 7=true := by decide +kernel
theorem nested_asym_11 : fastScan (asymAccept 11) 9 52 0 Moments.empty=true := by
  apply asym_first_complete
  intro i
  fin_cases i
  · exact row_11_0
  · exact row_11_1
  · exact row_11_2
  · exact row_11_3
  · exact row_11_4
  · exact row_11_5
  · exact row_11_6
  · exact row_11_7
#print axioms nested_asym_11
end NestedExposure
