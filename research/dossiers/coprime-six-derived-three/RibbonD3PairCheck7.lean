import RibbonD3OrbitData
import RibbonD3PairData7
namespace RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairChecked210 : good pairCerts7[0]! ((pairLabels[210]!).1.inp 0 0) ((pairLabels[210]!).2.inp 0 0) := from_stored (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem pairChecked211 : good pairCerts7[1]! ((pairLabels[211]!).1.inp 0 0) ((pairLabels[211]!).2.inp 0 0) := from_stored (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem pairChecked212 : good pairCerts7[2]! ((pairLabels[212]!).1.inp 0 0) ((pairLabels[212]!).2.inp 0 0) := from_stored (by decide +kernel) (by decide +kernel) (by decide +kernel)
end RibbonD3Finite
