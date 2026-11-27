import HaarDerivedGirth22
namespace HaarDerivedGirth22
open HaarSharpLamp (scan)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 200000000 in
theorem check2 : scan (table 2) = true := by decide +kernel
#print axioms check2
end HaarDerivedGirth22
