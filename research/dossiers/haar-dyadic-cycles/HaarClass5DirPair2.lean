import HaarClass5DirTables
namespace HaarClass5DirTables
set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem pairs2 : ∀ (i j : Fin 64), pair 2 i j := by decide +kernel
end HaarClass5DirTables
#print axioms HaarClass5DirTables.pairs2
