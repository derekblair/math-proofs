import Color13Data
namespace IU
set_option maxRecDepth 16000
set_option maxHeartbeats 0
theorem slice12 : packed (outsideSlice 13 2 2 3072 256) = packed (paintSlice pc13.flatten 3072 256) := by decide +kernel
theorem slice13 : packed (outsideSlice 13 2 2 3328 256) = packed (paintSlice pc13.flatten 3328 256) := by decide +kernel
theorem slice14 : packed (outsideSlice 13 2 2 3584 256) = packed (paintSlice pc13.flatten 3584 256) := by decide +kernel
theorem slice15 : packed (outsideSlice 13 2 2 3840 256) = packed (paintSlice pc13.flatten 3840 256) := by decide +kernel

end IU
