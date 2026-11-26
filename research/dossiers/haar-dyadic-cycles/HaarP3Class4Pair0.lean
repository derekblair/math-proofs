import HaarP3Class4Rows
namespace HaarP3Class4Rows
set_option maxRecDepth 35000 in
set_option maxHeartbeats 5000000 in
theorem check0 : ∀ i j : Fin 64, check 0 i j := by decide +kernel
end HaarP3Class4Rows
