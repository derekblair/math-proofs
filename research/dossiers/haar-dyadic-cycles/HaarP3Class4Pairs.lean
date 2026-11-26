import HaarP3Class4Pair0
import HaarP3Class4Pair1
import HaarP3Class4Pair2
import HaarP3Class4Pair3
namespace HaarP3Class4Rows
theorem all_pairs (t : Fin 4) (i j : Fin 64) : check t i j := by
  fin_cases t
  · exact check0 i j
  · exact check1 i j
  · exact check2 i j
  · exact check3 i j
end HaarP3Class4Rows
#print axioms HaarP3Class4Rows.all_pairs
