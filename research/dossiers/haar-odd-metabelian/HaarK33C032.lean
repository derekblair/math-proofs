import HaarK33Data
namespace HaarK33Data
open HaarK33DAG HaarK33Voltage
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
theorem C032valid (i : Nat) (_lo : 32 ≤ i) (_hi : i < 48) : valid D i := by
  by_cases h32_48 : i < 40
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
end HaarK33Data
