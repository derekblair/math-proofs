import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
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
private theorem ok64 : valid D 64 := by decide +kernel
private theorem ok65 : valid D 65 := by decide +kernel
private theorem ok66 : valid D 66 := by decide +kernel
private theorem ok67 : valid D 67 := by decide +kernel
private theorem ok68 : valid D 68 := by decide +kernel
private theorem ok69 : valid D 69 := by decide +kernel
private theorem ok70 : valid D 70 := by decide +kernel
private theorem ok71 : valid D 71 := by decide +kernel
theorem C048valid (i : Nat) (_lo : 48 ≤ i) (_hi : i < 72) : valid D i := by
  by_cases h48_72 : i < 60
  · by_cases h48_60 : i < 54
    · by_cases h48_54 : i < 51
      · by_cases h48_51 : i < 49
        · have e : i = 48 := by omega
          subst i
          exact ok48
        · by_cases h49_51 : i < 50
          · have e : i = 49 := by omega
            subst i
            exact ok49
          · have e : i = 50 := by omega
            subst i
            exact ok50
      · by_cases h51_54 : i < 52
        · have e : i = 51 := by omega
          subst i
          exact ok51
        · by_cases h52_54 : i < 53
          · have e : i = 52 := by omega
            subst i
            exact ok52
          · have e : i = 53 := by omega
            subst i
            exact ok53
    · by_cases h54_60 : i < 57
      · by_cases h54_57 : i < 55
        · have e : i = 54 := by omega
          subst i
          exact ok54
        · by_cases h55_57 : i < 56
          · have e : i = 55 := by omega
            subst i
            exact ok55
          · have e : i = 56 := by omega
            subst i
            exact ok56
      · by_cases h57_60 : i < 58
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
  · by_cases h60_72 : i < 66
    · by_cases h60_66 : i < 63
      · by_cases h60_63 : i < 61
        · have e : i = 60 := by omega
          subst i
          exact ok60
        · by_cases h61_63 : i < 62
          · have e : i = 61 := by omega
            subst i
            exact ok61
          · have e : i = 62 := by omega
            subst i
            exact ok62
      · by_cases h63_66 : i < 64
        · have e : i = 63 := by omega
          subst i
          exact ok63
        · by_cases h64_66 : i < 65
          · have e : i = 64 := by omega
            subst i
            exact ok64
          · have e : i = 65 := by omega
            subst i
            exact ok65
    · by_cases h66_72 : i < 69
      · by_cases h66_69 : i < 67
        · have e : i = 66 := by omega
          subst i
          exact ok66
        · by_cases h67_69 : i < 68
          · have e : i = 67 := by omega
            subst i
            exact ok67
          · have e : i = 68 := by omega
            subst i
            exact ok68
      · by_cases h69_72 : i < 70
        · have e : i = 69 := by omega
          subst i
          exact ok69
        · by_cases h70_72 : i < 71
          · have e : i = 70 := by omega
            subst i
            exact ok70
          · have e : i = 71 := by omega
            subst i
            exact ok71
end HaarHoneyData
