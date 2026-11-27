import HaarDerivedBaseFast
namespace HaarDerivedGirth22
open HaarSharpLamp (scan words)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 200000000 in
theorem fast9 : scan (sortedFast 9) = true := by decide +kernel
set_option maxRecDepth 120000 in
theorem len9 : (words 9 none).length≤2^11 := by decide +kernel
#print axioms fast9
end HaarDerivedGirth22
