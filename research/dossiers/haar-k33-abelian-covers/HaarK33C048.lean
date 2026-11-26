import HaarK33Data
namespace HaarK33Data
open HaarK33DAG HaarK33Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok48 : valid D 48 := by decide +kernel
private theorem ok49 : valid D 49 := by decide +kernel
private theorem ok50 : valid D 50 := by decide +kernel
private theorem ok51 : valid D 51 := by decide +kernel
private theorem ok52 : valid D 52 := by decide +kernel
private theorem ok53 : valid D 53 := by decide +kernel
private theorem ok54 : valid D 54 := by decide +kernel
private theorem ok55 : valid D 55 := by decide +kernel
private theorem ok56 : valid D 56 := by decide +kernel
private theorem ok57 : valid D 57 := by decide +kernel
private theorem ok58 : valid D 58 := by decide +kernel
private theorem ok59 : valid D 59 := by decide +kernel
private theorem ok60 : valid D 60 := by decide +kernel
private theorem ok61 : valid D 61 := by decide +kernel
private theorem ok62 : valid D 62 := by decide +kernel
private theorem ok63 : valid D 63 := by decide +kernel
theorem C048valid (i : Nat) (_lo : 48 ≤ i) (_hi : i < 64) : valid D i := by
  by_cases h48_64 : i < 56
  · by_cases h48_56 : i < 52
    · by_cases h48_52 : i < 50
      · by_cases h48_50 : i < 49
        · have e : i = 48 := by omega
          subst i
          exact ok48
        · have e : i = 49 := by omega
          subst i
          exact ok49
      · by_cases h50_52 : i < 51
        · have e : i = 50 := by omega
          subst i
          exact ok50
        · have e : i = 51 := by omega
          subst i
          exact ok51
    · by_cases h52_56 : i < 54
      · by_cases h52_54 : i < 53
        · have e : i = 52 := by omega
          subst i
          exact ok52
        · have e : i = 53 := by omega
          subst i
          exact ok53
      · by_cases h54_56 : i < 55
        · have e : i = 54 := by omega
          subst i
          exact ok54
        · have e : i = 55 := by omega
          subst i
          exact ok55
  · by_cases h56_64 : i < 60
    · by_cases h56_60 : i < 58
      · by_cases h56_58 : i < 57
        · have e : i = 56 := by omega
          subst i
          exact ok56
        · have e : i = 57 := by omega
          subst i
          exact ok57
      · by_cases h58_60 : i < 59
        · have e : i = 58 := by omega
          subst i
          exact ok58
        · have e : i = 59 := by omega
          subst i
          exact ok59
    · by_cases h60_64 : i < 62
      · by_cases h60_62 : i < 61
        · have e : i = 60 := by omega
          subst i
          exact ok60
        · have e : i = 61 := by omega
          subst i
          exact ok61
      · by_cases h62_64 : i < 63
        · have e : i = 62 := by omega
          subst i
          exact ok62
        · have e : i = 63 := by omega
          subst i
          exact ok63
end HaarK33Data
