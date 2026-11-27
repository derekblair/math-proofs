import RibbonD3WideOrbitCheckCore
namespace RibbonD3WideFinite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairOrbit2 (i : Fin 8) : PairOrbit (pairChunk 16 i) := by
  fin_cases i <;> decide +kernel
theorem jetOrbit2 (i : Fin 8) : JetOrbit (pairChunk 16 i) := by
  fin_cases i <;> decide +kernel
end RibbonD3WideFinite
