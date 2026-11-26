import RibbonD3OrbitCheckCore
namespace RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairOrbit5 (i : Fin 8) : PairOrbit (pairChunk 40 i) := by
  fin_cases i <;> decide +kernel
theorem jetOrbit5 (i : Fin 8) : JetOrbit (pairChunk 40 i) := by
  fin_cases i <;> decide +kernel
end RibbonD3Finite
