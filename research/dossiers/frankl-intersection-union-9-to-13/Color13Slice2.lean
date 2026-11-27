import Color13Data
namespace IU
set_option maxRecDepth 16000
set_option maxHeartbeats 0
theorem slice8 : packed (outsideSlice 13 2 2 2048 256) = packed (paintSlice pc13.flatten 2048 256) := by decide +kernel
theorem slice9 : packed (outsideSlice 13 2 2 2304 256) = packed (paintSlice pc13.flatten 2304 256) := by decide +kernel
theorem slice10 : packed (outsideSlice 13 2 2 2560 256) = packed (paintSlice pc13.flatten 2560 256) := by decide +kernel
theorem slice11 : packed (outsideSlice 13 2 2 2816 256) = packed (paintSlice pc13.flatten 2816 256) := by decide +kernel

end IU
