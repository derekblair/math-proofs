import HaarDerivedGirth22
namespace HaarDerivedGirth22
open HaarSharpLamp (scan)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 200000000 in
theorem check4 : scan (table 4) = true := by decide +kernel
#print axioms check4
end HaarDerivedGirth22
