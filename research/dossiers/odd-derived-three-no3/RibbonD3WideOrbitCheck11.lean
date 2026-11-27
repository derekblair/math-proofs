import RibbonD3WideOrbitCheckCore
namespace RibbonD3WideFinite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairOrbit11 (i : Fin 8) : PairOrbit (pairChunk 88 i) := by
  fin_cases i <;> decide +kernel
theorem jetOrbit11 (i : Fin 8) : JetOrbit (pairChunk 88 i) := by
  fin_cases i <;> decide +kernel
end RibbonD3WideFinite
