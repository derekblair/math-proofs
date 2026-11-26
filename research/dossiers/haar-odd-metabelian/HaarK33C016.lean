import HaarK33Data
namespace HaarK33Data
open HaarK33DAG HaarK33Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok16 : valid D 16 := by decide +kernel
private theorem ok17 : valid D 17 := by decide +kernel
private theorem ok18 : valid D 18 := by decide +kernel
private theorem ok19 : valid D 19 := by decide +kernel
private theorem ok20 : valid D 20 := by decide +kernel
private theorem ok21 : valid D 21 := by decide +kernel
private theorem ok22 : valid D 22 := by decide +kernel
private theorem ok23 : valid D 23 := by decide +kernel
private theorem ok24 : valid D 24 := by decide +kernel
private theorem ok25 : valid D 25 := by decide +kernel
private theorem ok26 : valid D 26 := by decide +kernel
private theorem ok27 : valid D 27 := by decide +kernel
private theorem ok28 : valid D 28 := by decide +kernel
private theorem ok29 : valid D 29 := by decide +kernel
private theorem ok30 : valid D 30 := by decide +kernel
private theorem ok31 : valid D 31 := by decide +kernel
theorem C016valid (i : Nat) (_lo : 16 ≤ i) (_hi : i < 32) : valid D i := by
  by_cases h16_32 : i < 24
  · by_cases h16_24 : i < 20
    · by_cases h16_20 : i < 18
      · by_cases h16_18 : i < 17
        · have e : i = 16 := by omega
          subst i
          exact ok16
        · have e : i = 17 := by omega
          subst i
          exact ok17
      · by_cases h18_20 : i < 19
        · have e : i = 18 := by omega
          subst i
          exact ok18
        · have e : i = 19 := by omega
          subst i
          exact ok19
    · by_cases h20_24 : i < 22
      · by_cases h20_22 : i < 21
        · have e : i = 20 := by omega
          subst i
          exact ok20
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
  · by_cases h24_32 : i < 28
    · by_cases h24_28 : i < 26
      · by_cases h24_26 : i < 25
        · have e : i = 24 := by omega
          subst i
          exact ok24
        · have e : i = 25 := by omega
          subst i
          exact ok25
      · by_cases h26_28 : i < 27
        · have e : i = 26 := by omega
          subst i
          exact ok26
        · have e : i = 27 := by omega
          subst i
          exact ok27
    · by_cases h28_32 : i < 30
      · by_cases h28_30 : i < 29
        · have e : i = 28 := by omega
          subst i
          exact ok28
        · have e : i = 29 := by omega
          subst i
          exact ok29
      · by_cases h30_32 : i < 31
        · have e : i = 30 := by omega
          subst i
          exact ok30
        · have e : i = 31 := by omega
          subst i
          exact ok31
end HaarK33Data
