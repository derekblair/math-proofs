import HaarC5Data
namespace HaarC5Data
open HaarC5DAG HaarC5Voltage
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
private theorem ok16 : valid D 16 := by decide +kernel
private theorem ok17 : valid D 17 := by decide +kernel
private theorem ok18 : valid D 18 := by decide +kernel
private theorem ok19 : valid D 19 := by decide +kernel
private theorem ok20 : valid D 20 := by decide +kernel
private theorem ok21 : valid D 21 := by decide +kernel
private theorem ok22 : valid D 22 := by decide +kernel
private theorem ok23 : valid D 23 := by decide +kernel
theorem C000valid (i : Nat) (_lo : 0 ≤ i) (_hi : i < 24) : valid D i := by
  by_cases h0_24 : i < 12
  · by_cases h0_12 : i < 6
    · by_cases h0_6 : i < 3
      · by_cases h0_3 : i < 1
        · have e : i = 0 := by omega
          subst i
          exact ok0
        · by_cases h1_3 : i < 2
          · have e : i = 1 := by omega
            subst i
            exact ok1
          · have e : i = 2 := by omega
            subst i
            exact ok2
      · by_cases h3_6 : i < 4
        · have e : i = 3 := by omega
          subst i
          exact ok3
        · by_cases h4_6 : i < 5
          · have e : i = 4 := by omega
            subst i
            exact ok4
          · have e : i = 5 := by omega
            subst i
            exact ok5
    · by_cases h6_12 : i < 9
      · by_cases h6_9 : i < 7
        · have e : i = 6 := by omega
          subst i
          exact ok6
        · by_cases h7_9 : i < 8
          · have e : i = 7 := by omega
            subst i
            exact ok7
          · have e : i = 8 := by omega
            subst i
            exact ok8
      · by_cases h9_12 : i < 10
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
  · by_cases h12_24 : i < 18
    · by_cases h12_18 : i < 15
      · by_cases h12_15 : i < 13
        · have e : i = 12 := by omega
          subst i
          exact ok12
        · by_cases h13_15 : i < 14
          · have e : i = 13 := by omega
            subst i
            exact ok13
          · have e : i = 14 := by omega
            subst i
            exact ok14
      · by_cases h15_18 : i < 16
        · have e : i = 15 := by omega
          subst i
          exact ok15
        · by_cases h16_18 : i < 17
          · have e : i = 16 := by omega
            subst i
            exact ok16
          · have e : i = 17 := by omega
            subst i
            exact ok17
    · by_cases h18_24 : i < 21
      · by_cases h18_21 : i < 19
        · have e : i = 18 := by omega
          subst i
          exact ok18
        · by_cases h19_21 : i < 20
          · have e : i = 19 := by omega
            subst i
            exact ok19
          · have e : i = 20 := by omega
            subst i
            exact ok20
      · by_cases h21_24 : i < 22
        · have e : i = 21 := by omega
          subst i
          exact ok21
        · by_cases h22_24 : i < 23
          · have e : i = 22 := by omega
            subst i
            exact ok22
          · have e : i = 23 := by omega
            subst i
            exact ok23
end HaarC5Data
