import HaarClass5DirPair0
import HaarClass5DirPair1
import HaarClass5DirPair2
import HaarClass5DirPair3
namespace HaarClass5DirTables
theorem pairs (t : Fin 4) (i j : Fin 64) : pair t i j := by
  fin_cases t
  · exact pairs0 i j
  · exact pairs1 i j
  · exact pairs2 i j
  · exact pairs3 i j
end HaarClass5DirTables
