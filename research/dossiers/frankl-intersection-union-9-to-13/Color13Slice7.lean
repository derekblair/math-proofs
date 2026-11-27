import Color13Data
namespace IU
set_option maxRecDepth 16000
set_option maxHeartbeats 0
theorem slice28 : packed (outsideSlice 13 2 2 7168 256) = packed (paintSlice pc13.flatten 7168 256) := by decide +kernel
theorem slice29 : packed (outsideSlice 13 2 2 7424 256) = packed (paintSlice pc13.flatten 7424 256) := by decide +kernel
theorem slice30 : packed (outsideSlice 13 2 2 7680 256) = packed (paintSlice pc13.flatten 7680 256) := by decide +kernel
theorem slice31 : packed (outsideSlice 13 2 2 7936 256) = packed (paintSlice pc13.flatten 7936 256) := by decide +kernel

end IU
