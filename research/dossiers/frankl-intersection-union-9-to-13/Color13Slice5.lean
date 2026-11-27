import Color13Data
namespace IU
set_option maxRecDepth 16000
set_option maxHeartbeats 0
theorem slice20 : packed (outsideSlice 13 2 2 5120 256) = packed (paintSlice pc13.flatten 5120 256) := by decide +kernel
theorem slice21 : packed (outsideSlice 13 2 2 5376 256) = packed (paintSlice pc13.flatten 5376 256) := by decide +kernel
theorem slice22 : packed (outsideSlice 13 2 2 5632 256) = packed (paintSlice pc13.flatten 5632 256) := by decide +kernel
theorem slice23 : packed (outsideSlice 13 2 2 5888 256) = packed (paintSlice pc13.flatten 5888 256) := by decide +kernel

end IU
