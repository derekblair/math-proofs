import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1008 : valid D 1008 := by decide +kernel
private theorem ok1009 : valid D 1009 := by decide +kernel
private theorem ok1010 : valid D 1010 := by decide +kernel
private theorem ok1011 : valid D 1011 := by decide +kernel
private theorem ok1012 : valid D 1012 := by decide +kernel
private theorem ok1013 : valid D 1013 := by decide +kernel
private theorem ok1014 : valid D 1014 := by decide +kernel
private theorem ok1015 : valid D 1015 := by decide +kernel
private theorem ok1016 : valid D 1016 := by decide +kernel
private theorem ok1017 : valid D 1017 := by decide +kernel
private theorem ok1018 : valid D 1018 := by decide +kernel
private theorem ok1019 : valid D 1019 := by decide +kernel
private theorem ok1020 : valid D 1020 := by decide +kernel
private theorem ok1021 : valid D 1021 := by decide +kernel
private theorem ok1022 : valid D 1022 := by decide +kernel
private theorem ok1023 : valid D 1023 := by decide +kernel
private theorem ok1024 : valid D 1024 := by decide +kernel
private theorem ok1025 : valid D 1025 := by decide +kernel
private theorem ok1026 : valid D 1026 := by decide +kernel
private theorem ok1027 : valid D 1027 := by decide +kernel
private theorem ok1028 : valid D 1028 := by decide +kernel
private theorem ok1029 : valid D 1029 := by decide +kernel
private theorem ok1030 : valid D 1030 := by decide +kernel
private theorem ok1031 : valid D 1031 := by decide +kernel
theorem C1008valid (i : Nat) (_lo : 1008 ≤ i) (_hi : i < 1032) : valid D i := by
  by_cases h1008_1032 : i < 1020
  · by_cases h1008_1020 : i < 1014
    · by_cases h1008_1014 : i < 1011
      · by_cases h1008_1011 : i < 1009
        · have e : i = 1008 := by omega
          subst i
          exact ok1008
        · by_cases h1009_1011 : i < 1010
          · have e : i = 1009 := by omega
            subst i
            exact ok1009
          · have e : i = 1010 := by omega
            subst i
            exact ok1010
      · by_cases h1011_1014 : i < 1012
        · have e : i = 1011 := by omega
          subst i
          exact ok1011
        · by_cases h1012_1014 : i < 1013
          · have e : i = 1012 := by omega
            subst i
            exact ok1012
          · have e : i = 1013 := by omega
            subst i
            exact ok1013
    · by_cases h1014_1020 : i < 1017
      · by_cases h1014_1017 : i < 1015
        · have e : i = 1014 := by omega
          subst i
          exact ok1014
        · by_cases h1015_1017 : i < 1016
          · have e : i = 1015 := by omega
            subst i
            exact ok1015
          · have e : i = 1016 := by omega
            subst i
            exact ok1016
      · by_cases h1017_1020 : i < 1018
        · have e : i = 1017 := by omega
          subst i
          exact ok1017
        · by_cases h1018_1020 : i < 1019
          · have e : i = 1018 := by omega
            subst i
            exact ok1018
          · have e : i = 1019 := by omega
            subst i
            exact ok1019
  · by_cases h1020_1032 : i < 1026
    · by_cases h1020_1026 : i < 1023
      · by_cases h1020_1023 : i < 1021
        · have e : i = 1020 := by omega
          subst i
          exact ok1020
        · by_cases h1021_1023 : i < 1022
          · have e : i = 1021 := by omega
            subst i
            exact ok1021
          · have e : i = 1022 := by omega
            subst i
            exact ok1022
      · by_cases h1023_1026 : i < 1024
        · have e : i = 1023 := by omega
          subst i
          exact ok1023
        · by_cases h1024_1026 : i < 1025
          · have e : i = 1024 := by omega
            subst i
            exact ok1024
          · have e : i = 1025 := by omega
            subst i
            exact ok1025
    · by_cases h1026_1032 : i < 1029
      · by_cases h1026_1029 : i < 1027
        · have e : i = 1026 := by omega
          subst i
          exact ok1026
        · by_cases h1027_1029 : i < 1028
          · have e : i = 1027 := by omega
            subst i
            exact ok1027
          · have e : i = 1028 := by omega
            subst i
            exact ok1028
      · by_cases h1029_1032 : i < 1030
        · have e : i = 1029 := by omega
          subst i
          exact ok1029
        · by_cases h1030_1032 : i < 1031
          · have e : i = 1030 := by omega
            subst i
            exact ok1030
          · have e : i = 1031 := by omega
            subst i
            exact ok1031
end HaarHoneyData
