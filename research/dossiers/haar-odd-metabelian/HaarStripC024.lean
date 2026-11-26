import HaarStripData
namespace HaarStripData
open HaarStripDAG HaarStripVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok24 : valid D 24 := by decide +kernel
private theorem ok25 : valid D 25 := by decide +kernel
private theorem ok26 : valid D 26 := by decide +kernel
private theorem ok27 : valid D 27 := by decide +kernel
private theorem ok28 : valid D 28 := by decide +kernel
private theorem ok29 : valid D 29 := by decide +kernel
private theorem ok30 : valid D 30 := by decide +kernel
private theorem ok31 : valid D 31 := by decide +kernel
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
theorem C024valid (i : Nat) (_lo : 24 ≤ i) (_hi : i < 48) : valid D i := by
  by_cases h24_48 : i < 36
  · by_cases h24_36 : i < 30
    · by_cases h24_30 : i < 27
      · by_cases h24_27 : i < 25
        · have e : i = 24 := by omega
          subst i
          exact ok24
        · by_cases h25_27 : i < 26
          · have e : i = 25 := by omega
            subst i
            exact ok25
          · have e : i = 26 := by omega
            subst i
            exact ok26
      · by_cases h27_30 : i < 28
        · have e : i = 27 := by omega
          subst i
          exact ok27
        · by_cases h28_30 : i < 29
          · have e : i = 28 := by omega
            subst i
            exact ok28
          · have e : i = 29 := by omega
            subst i
            exact ok29
    · by_cases h30_36 : i < 33
      · by_cases h30_33 : i < 31
        · have e : i = 30 := by omega
          subst i
          exact ok30
        · by_cases h31_33 : i < 32
          · have e : i = 31 := by omega
            subst i
            exact ok31
          · have e : i = 32 := by omega
            subst i
            exact ok32
      · by_cases h33_36 : i < 34
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
  · by_cases h36_48 : i < 42
    · by_cases h36_42 : i < 39
      · by_cases h36_39 : i < 37
        · have e : i = 36 := by omega
          subst i
          exact ok36
        · by_cases h37_39 : i < 38
          · have e : i = 37 := by omega
            subst i
            exact ok37
          · have e : i = 38 := by omega
            subst i
            exact ok38
      · by_cases h39_42 : i < 40
        · have e : i = 39 := by omega
          subst i
          exact ok39
        · by_cases h40_42 : i < 41
          · have e : i = 40 := by omega
            subst i
            exact ok40
          · have e : i = 41 := by omega
            subst i
            exact ok41
    · by_cases h42_48 : i < 45
      · by_cases h42_45 : i < 43
        · have e : i = 42 := by omega
          subst i
          exact ok42
        · by_cases h43_45 : i < 44
          · have e : i = 43 := by omega
            subst i
            exact ok43
          · have e : i = 44 := by omega
            subst i
            exact ok44
      · by_cases h45_48 : i < 46
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
end HaarStripData
