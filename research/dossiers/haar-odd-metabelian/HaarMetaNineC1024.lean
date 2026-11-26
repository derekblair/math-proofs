import HaarMetaNineData
namespace HaarMetaNineData
open HaarMetaNineDAG HaarMetaNineVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1024 : valid D 1024 := by decide +kernel
theorem C1024valid (i : Nat) (_lo : 1024 ≤ i) (_hi : i < 1025) : valid D i := by
  have e : i = 1024 := by omega
  subst i
  exact ok1024
end HaarMetaNineData
