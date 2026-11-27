import HaarDerivedGirth22
namespace HaarDerivedGirth22
open HaarSharpLamp (scan)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 200000000 in
theorem check8 : scan (table 8) = true := by decide +kernel
#print axioms check8
end HaarDerivedGirth22
