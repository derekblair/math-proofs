import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1056 : valid D 1056 := by decide +kernel
private theorem ok1057 : valid D 1057 := by decide +kernel
private theorem ok1058 : valid D 1058 := by decide +kernel
private theorem ok1059 : valid D 1059 := by decide +kernel
private theorem ok1060 : valid D 1060 := by decide +kernel
private theorem ok1061 : valid D 1061 := by decide +kernel
private theorem ok1062 : valid D 1062 := by decide +kernel
private theorem ok1063 : valid D 1063 := by decide +kernel
private theorem ok1064 : valid D 1064 := by decide +kernel
private theorem ok1065 : valid D 1065 := by decide +kernel
private theorem ok1066 : valid D 1066 := by decide +kernel
private theorem ok1067 : valid D 1067 := by decide +kernel
private theorem ok1068 : valid D 1068 := by decide +kernel
private theorem ok1069 : valid D 1069 := by decide +kernel
private theorem ok1070 : valid D 1070 := by decide +kernel
private theorem ok1071 : valid D 1071 := by decide +kernel
private theorem ok1072 : valid D 1072 := by decide +kernel
private theorem ok1073 : valid D 1073 := by decide +kernel
private theorem ok1074 : valid D 1074 := by decide +kernel
private theorem ok1075 : valid D 1075 := by decide +kernel
private theorem ok1076 : valid D 1076 := by decide +kernel
private theorem ok1077 : valid D 1077 := by decide +kernel
private theorem ok1078 : valid D 1078 := by decide +kernel
private theorem ok1079 : valid D 1079 := by decide +kernel
theorem C1056valid (i : Nat) (_lo : 1056 ≤ i) (_hi : i < 1080) : valid D i := by
  by_cases h1056_1080 : i < 1068
  · by_cases h1056_1068 : i < 1062
    · by_cases h1056_1062 : i < 1059
      · by_cases h1056_1059 : i < 1057
        · have e : i = 1056 := by omega
          subst i
          exact ok1056
        · by_cases h1057_1059 : i < 1058
          · have e : i = 1057 := by omega
            subst i
            exact ok1057
          · have e : i = 1058 := by omega
            subst i
            exact ok1058
      · by_cases h1059_1062 : i < 1060
        · have e : i = 1059 := by omega
          subst i
          exact ok1059
        · by_cases h1060_1062 : i < 1061
          · have e : i = 1060 := by omega
            subst i
            exact ok1060
          · have e : i = 1061 := by omega
            subst i
            exact ok1061
    · by_cases h1062_1068 : i < 1065
      · by_cases h1062_1065 : i < 1063
        · have e : i = 1062 := by omega
          subst i
          exact ok1062
        · by_cases h1063_1065 : i < 1064
          · have e : i = 1063 := by omega
            subst i
            exact ok1063
          · have e : i = 1064 := by omega
            subst i
            exact ok1064
      · by_cases h1065_1068 : i < 1066
        · have e : i = 1065 := by omega
          subst i
          exact ok1065
        · by_cases h1066_1068 : i < 1067
          · have e : i = 1066 := by omega
            subst i
            exact ok1066
          · have e : i = 1067 := by omega
            subst i
            exact ok1067
  · by_cases h1068_1080 : i < 1074
    · by_cases h1068_1074 : i < 1071
      · by_cases h1068_1071 : i < 1069
        · have e : i = 1068 := by omega
          subst i
          exact ok1068
        · by_cases h1069_1071 : i < 1070
          · have e : i = 1069 := by omega
            subst i
            exact ok1069
          · have e : i = 1070 := by omega
            subst i
            exact ok1070
      · by_cases h1071_1074 : i < 1072
        · have e : i = 1071 := by omega
          subst i
          exact ok1071
        · by_cases h1072_1074 : i < 1073
          · have e : i = 1072 := by omega
            subst i
            exact ok1072
          · have e : i = 1073 := by omega
            subst i
            exact ok1073
    · by_cases h1074_1080 : i < 1077
      · by_cases h1074_1077 : i < 1075
        · have e : i = 1074 := by omega
          subst i
          exact ok1074
        · by_cases h1075_1077 : i < 1076
          · have e : i = 1075 := by omega
            subst i
            exact ok1075
          · have e : i = 1076 := by omega
            subst i
            exact ok1076
      · by_cases h1077_1080 : i < 1078
        · have e : i = 1077 := by omega
          subst i
          exact ok1077
        · by_cases h1078_1080 : i < 1079
          · have e : i = 1078 := by omega
            subst i
            exact ok1078
          · have e : i = 1079 := by omega
            subst i
            exact ok1079
end HaarHoneyData
