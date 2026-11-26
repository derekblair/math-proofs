import HaarMetaTorusData
namespace HaarMetaTorusData
open HaarMetaTorusDAG HaarMetaTorusVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok544 : valid D 544 := by decide +kernel
private theorem ok545 : valid D 545 := by decide +kernel
private theorem ok546 : valid D 546 := by decide +kernel
theorem C544valid (i : Nat) (_lo : 544 ≤ i) (_hi : i < 547) : valid D i := by
  by_cases h544_547 : i < 545
  · have e : i = 544 := by omega
    subst i
    exact ok544
  · by_cases h545_547 : i < 546
    · have e : i = 545 := by omega
      subst i
      exact ok545
    · have e : i = 546 := by omega
      subst i
      exact ok546
end HaarMetaTorusData
