import Color13Data
namespace IU
set_option maxRecDepth 16000
set_option maxHeartbeats 0
theorem slice16 : packed (outsideSlice 13 2 2 4096 256) = packed (paintSlice pc13.flatten 4096 256) := by decide +kernel
theorem slice17 : packed (outsideSlice 13 2 2 4352 256) = packed (paintSlice pc13.flatten 4352 256) := by decide +kernel
theorem slice18 : packed (outsideSlice 13 2 2 4608 256) = packed (paintSlice pc13.flatten 4608 256) := by decide +kernel
theorem slice19 : packed (outsideSlice 13 2 2 4864 256) = packed (paintSlice pc13.flatten 4864 256) := by decide +kernel

end IU
