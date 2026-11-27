import HaarK33Data
namespace HaarK33Data
open HaarK33DAG HaarK33Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok0 : valid D 0 := by decide +kernel
private theorem ok1 : valid D 1 := by decide +kernel
private theorem ok2 : valid D 2 := by decide +kernel
private theorem ok3 : valid D 3 := by decide +kernel
private theorem ok4 : valid D 4 := by decide +kernel
private theorem ok5 : valid D 5 := by decide +kernel
private theorem ok6 : valid D 6 := by decide +kernel
private theorem ok7 : valid D 7 := by decide +kernel
private theorem ok8 : valid D 8 := by decide +kernel
private theorem ok9 : valid D 9 := by decide +kernel
private theorem ok10 : valid D 10 := by decide +kernel
private theorem ok11 : valid D 11 := by decide +kernel
private theorem ok12 : valid D 12 := by decide +kernel
private theorem ok13 : valid D 13 := by decide +kernel
private theorem ok14 : valid D 14 := by decide +kernel
private theorem ok15 : valid D 15 := by decide +kernel
theorem C000valid (i : Nat) (_lo : 0 ≤ i) (_hi : i < 16) : valid D i := by
  by_cases h0_16 : i < 8
  · by_cases h0_8 : i < 4
    · by_cases h0_4 : i < 2
      · by_cases h0_2 : i < 1
        · have e : i = 0 := by omega
          subst i
          exact ok0
        · have e : i = 1 := by omega
          subst i
          exact ok1
      · by_cases h2_4 : i < 3
        · have e : i = 2 := by omega
          subst i
          exact ok2
        · have e : i = 3 := by omega
          subst i
          exact ok3
    · by_cases h4_8 : i < 6
      · by_cases h4_6 : i < 5
        · have e : i = 4 := by omega
          subst i
          exact ok4
        · have e : i = 5 := by omega
          subst i
          exact ok5
      · by_cases h6_8 : i < 7
        · have e : i = 6 := by omega
          subst i
          exact ok6
        · have e : i = 7 := by omega
          subst i
          exact ok7
  · by_cases h8_16 : i < 12
    · by_cases h8_12 : i < 10
      · by_cases h8_10 : i < 9
        · have e : i = 8 := by omega
          subst i
          exact ok8
        · have e : i = 9 := by omega
          subst i
          exact ok9
      · by_cases h10_12 : i < 11
        · have e : i = 10 := by omega
          subst i
          exact ok10
        · have e : i = 11 := by omega
          subst i
          exact ok11
    · by_cases h12_16 : i < 14
      · by_cases h12_14 : i < 13
        · have e : i = 12 := by omega
          subst i
          exact ok12
        · have e : i = 13 := by omega
          subst i
          exact ok13
      · by_cases h14_16 : i < 15
        · have e : i = 14 := by omega
          subst i
          exact ok14
        · have e : i = 15 := by omega
          subst i
          exact ok15
end HaarK33Data
