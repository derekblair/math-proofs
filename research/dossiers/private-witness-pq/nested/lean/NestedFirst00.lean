import NestedAsymBranch
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
namespace NestedExposure
set_option maxHeartbeats 0
set_option maxRecDepth 16000
private theorem row_00_0 : asymFirst 0 0=true := by decide +kernel
private theorem row_00_1 : asymFirst 0 1=true := by decide +kernel
private theorem row_00_2 : asymFirst 0 2=true := by decide +kernel
private theorem row_00_3 : asymFirst 0 3=true := by decide +kernel
private theorem row_00_4 : asymFirst 0 4=true := by decide +kernel
private theorem row_00_5 : asymFirst 0 5=true := by decide +kernel
private theorem row_00_6 : asymFirst 0 6=true := by decide +kernel
private theorem row_00_7 : asymFirst 0 7=true := by decide +kernel
theorem nested_asym_00 : fastScan (asymAccept 0) 9 63 0 Moments.empty=true := by
  apply asym_first_complete
  intro i
  fin_cases i
  · exact row_00_0
  · exact row_00_1
  · exact row_00_2
  · exact row_00_3
  · exact row_00_4
  · exact row_00_5
  · exact row_00_6
  · exact row_00_7
#print axioms nested_asym_00
end NestedExposure
