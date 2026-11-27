import Color13Data
namespace IU
set_option maxRecDepth 16000
set_option maxHeartbeats 0
theorem slice0 : packed (outsideSlice 13 2 2 0 256) = packed (paintSlice pc13.flatten 0 256) := by decide +kernel
theorem slice1 : packed (outsideSlice 13 2 2 256 256) = packed (paintSlice pc13.flatten 256 256) := by decide +kernel
theorem slice2 : packed (outsideSlice 13 2 2 512 256) = packed (paintSlice pc13.flatten 512 256) := by decide +kernel
theorem slice3 : packed (outsideSlice 13 2 2 768 256) = packed (paintSlice pc13.flatten 768 256) := by decide +kernel

end IU
