import HaarK33Data
namespace HaarK33Data
open HaarK33DAG HaarK33Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok256 : valid D 256 := by decide +kernel
private theorem ok257 : valid D 257 := by decide +kernel
private theorem ok258 : valid D 258 := by decide +kernel
theorem C256valid (i : Nat) (_lo : 256 ≤ i) (_hi : i < 259) : valid D i := by
  by_cases h256_259 : i < 257
  · have e : i = 256 := by omega
    subst i
    exact ok256
  · by_cases h257_259 : i < 258
    · have e : i = 257 := by omega
      subst i
      exact ok257
    · have e : i = 258 := by omega
      subst i
      exact ok258
end HaarK33Data
