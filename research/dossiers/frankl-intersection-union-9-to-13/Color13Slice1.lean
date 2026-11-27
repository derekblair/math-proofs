import Color13Data
namespace IU
set_option maxRecDepth 16000
set_option maxHeartbeats 0
theorem slice4 : packed (outsideSlice 13 2 2 1024 256) = packed (paintSlice pc13.flatten 1024 256) := by decide +kernel
theorem slice5 : packed (outsideSlice 13 2 2 1280 256) = packed (paintSlice pc13.flatten 1280 256) := by decide +kernel
theorem slice6 : packed (outsideSlice 13 2 2 1536 256) = packed (paintSlice pc13.flatten 1536 256) := by decide +kernel
theorem slice7 : packed (outsideSlice 13 2 2 1792 256) = packed (paintSlice pc13.flatten 1792 256) := by decide +kernel

end IU
