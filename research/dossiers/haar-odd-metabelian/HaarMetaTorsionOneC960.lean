import HaarMetaTorsionOneData
namespace HaarMetaTorsionOneData
open HaarMetaTorsionOneDAG HaarMetaTorsionOneVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok960 : valid D 960 := by decide +kernel
private theorem ok961 : valid D 961 := by decide +kernel
private theorem ok962 : valid D 962 := by decide +kernel
private theorem ok963 : valid D 963 := by decide +kernel
theorem C960valid (i : Nat) (_lo : 960 ≤ i) (_hi : i < 964) : valid D i := by
  by_cases h960_964 : i < 962
  · by_cases h960_962 : i < 961
    · have e : i = 960 := by omega
      subst i
      exact ok960
    · have e : i = 961 := by omega
      subst i
      exact ok961
  · by_cases h962_964 : i < 963
    · have e : i = 962 := by omega
      subst i
      exact ok962
    · have e : i = 963 := by omega
      subst i
      exact ok963
end HaarMetaTorsionOneData
