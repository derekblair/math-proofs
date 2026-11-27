import RibbonD3WideOrbitCheckCore
namespace RibbonD3WideFinite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairOrbit8 (i : Fin 8) : PairOrbit (pairChunk 64 i) := by
  fin_cases i <;> decide +kernel
theorem jetOrbit8 (i : Fin 8) : JetOrbit (pairChunk 64 i) := by
  fin_cases i <;> decide +kernel
end RibbonD3WideFinite
