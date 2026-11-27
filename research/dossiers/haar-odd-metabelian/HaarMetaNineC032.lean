import HaarMetaNineData
namespace HaarMetaNineData
open HaarMetaNineDAG HaarMetaNineVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok32 : valid D 32 := by decide +kernel
private theorem ok33 : valid D 33 := by decide +kernel
private theorem ok34 : valid D 34 := by decide +kernel
private theorem ok35 : valid D 35 := by decide +kernel
private theorem ok36 : valid D 36 := by decide +kernel
private theorem ok37 : valid D 37 := by decide +kernel
private theorem ok38 : valid D 38 := by decide +kernel
private theorem ok39 : valid D 39 := by decide +kernel
private theorem ok40 : valid D 40 := by decide +kernel
private theorem ok41 : valid D 41 := by decide +kernel
private theorem ok42 : valid D 42 := by decide +kernel
private theorem ok43 : valid D 43 := by decide +kernel
private theorem ok44 : valid D 44 := by decide +kernel
private theorem ok45 : valid D 45 := by decide +kernel
private theorem ok46 : valid D 46 := by decide +kernel
private theorem ok47 : valid D 47 := by decide +kernel
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
theorem C032valid (i : Nat) (_lo : 32 ≤ i) (_hi : i < 64) : valid D i := by
  by_cases h32_64 : i < 48
  · by_cases h32_48 : i < 40
    · by_cases h32_40 : i < 36
      · by_cases h32_36 : i < 34
        · by_cases h32_34 : i < 33
          · have e : i = 32 := by omega
            subst i
            exact ok32
          · have e : i = 33 := by omega
            subst i
            exact ok33
        · by_cases h34_36 : i < 35
          · have e : i = 34 := by omega
            subst i
            exact ok34
          · have e : i = 35 := by omega
            subst i
            exact ok35
      · by_cases h36_40 : i < 38
        · by_cases h36_38 : i < 37
          · have e : i = 36 := by omega
            subst i
            exact ok36
          · have e : i = 37 := by omega
            subst i
            exact ok37
        · by_cases h38_40 : i < 39
          · have e : i = 38 := by omega
            subst i
            exact ok38
          · have e : i = 39 := by omega
            subst i
            exact ok39
    · by_cases h40_48 : i < 44
      · by_cases h40_44 : i < 42
        · by_cases h40_42 : i < 41
          · have e : i = 40 := by omega
            subst i
            exact ok40
          · have e : i = 41 := by omega
            subst i
            exact ok41
        · by_cases h42_44 : i < 43
          · have e : i = 42 := by omega
            subst i
            exact ok42
          · have e : i = 43 := by omega
            subst i
            exact ok43
      · by_cases h44_48 : i < 46
        · by_cases h44_46 : i < 45
          · have e : i = 44 := by omega
            subst i
            exact ok44
          · have e : i = 45 := by omega
            subst i
            exact ok45
        · by_cases h46_48 : i < 47
          · have e : i = 46 := by omega
            subst i
            exact ok46
          · have e : i = 47 := by omega
            subst i
            exact ok47
  · by_cases h48_64 : i < 56
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
end HaarMetaNineData
