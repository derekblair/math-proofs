import Color13Data
namespace IU
set_option maxRecDepth 16000
set_option maxHeartbeats 0
theorem slice24 : packed (outsideSlice 13 2 2 6144 256) = packed (paintSlice pc13.flatten 6144 256) := by decide +kernel
theorem slice25 : packed (outsideSlice 13 2 2 6400 256) = packed (paintSlice pc13.flatten 6400 256) := by decide +kernel
theorem slice26 : packed (outsideSlice 13 2 2 6656 256) = packed (paintSlice pc13.flatten 6656 256) := by decide +kernel
theorem slice27 : packed (outsideSlice 13 2 2 6912 256) = packed (paintSlice pc13.flatten 6912 256) := by decide +kernel

end IU
