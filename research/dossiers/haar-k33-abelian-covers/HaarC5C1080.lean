import HaarC5Data
namespace HaarC5Data
open HaarC5DAG HaarC5Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1080 : valid D 1080 := by decide +kernel
private theorem ok1081 : valid D 1081 := by decide +kernel
private theorem ok1082 : valid D 1082 := by decide +kernel
private theorem ok1083 : valid D 1083 := by decide +kernel
private theorem ok1084 : valid D 1084 := by decide +kernel
private theorem ok1085 : valid D 1085 := by decide +kernel
private theorem ok1086 : valid D 1086 := by decide +kernel
private theorem ok1087 : valid D 1087 := by decide +kernel
private theorem ok1088 : valid D 1088 := by decide +kernel
private theorem ok1089 : valid D 1089 := by decide +kernel
private theorem ok1090 : valid D 1090 := by decide +kernel
private theorem ok1091 : valid D 1091 := by decide +kernel
private theorem ok1092 : valid D 1092 := by decide +kernel
private theorem ok1093 : valid D 1093 := by decide +kernel
private theorem ok1094 : valid D 1094 := by decide +kernel
private theorem ok1095 : valid D 1095 := by decide +kernel
private theorem ok1096 : valid D 1096 := by decide +kernel
private theorem ok1097 : valid D 1097 := by decide +kernel
private theorem ok1098 : valid D 1098 := by decide +kernel
private theorem ok1099 : valid D 1099 := by decide +kernel
private theorem ok1100 : valid D 1100 := by decide +kernel
private theorem ok1101 : valid D 1101 := by decide +kernel
private theorem ok1102 : valid D 1102 := by decide +kernel
private theorem ok1103 : valid D 1103 := by decide +kernel
theorem C1080valid (i : Nat) (_lo : 1080 ≤ i) (_hi : i < 1104) : valid D i := by
  by_cases h1080_1104 : i < 1092
  · by_cases h1080_1092 : i < 1086
    · by_cases h1080_1086 : i < 1083
      · by_cases h1080_1083 : i < 1081
        · have e : i = 1080 := by omega
          subst i
          exact ok1080
        · by_cases h1081_1083 : i < 1082
          · have e : i = 1081 := by omega
            subst i
            exact ok1081
          · have e : i = 1082 := by omega
            subst i
            exact ok1082
      · by_cases h1083_1086 : i < 1084
        · have e : i = 1083 := by omega
          subst i
          exact ok1083
        · by_cases h1084_1086 : i < 1085
          · have e : i = 1084 := by omega
            subst i
            exact ok1084
          · have e : i = 1085 := by omega
            subst i
            exact ok1085
    · by_cases h1086_1092 : i < 1089
      · by_cases h1086_1089 : i < 1087
        · have e : i = 1086 := by omega
          subst i
          exact ok1086
        · by_cases h1087_1089 : i < 1088
          · have e : i = 1087 := by omega
            subst i
            exact ok1087
          · have e : i = 1088 := by omega
            subst i
            exact ok1088
      · by_cases h1089_1092 : i < 1090
        · have e : i = 1089 := by omega
          subst i
          exact ok1089
        · by_cases h1090_1092 : i < 1091
          · have e : i = 1090 := by omega
            subst i
            exact ok1090
          · have e : i = 1091 := by omega
            subst i
            exact ok1091
  · by_cases h1092_1104 : i < 1098
    · by_cases h1092_1098 : i < 1095
      · by_cases h1092_1095 : i < 1093
        · have e : i = 1092 := by omega
          subst i
          exact ok1092
        · by_cases h1093_1095 : i < 1094
          · have e : i = 1093 := by omega
            subst i
            exact ok1093
          · have e : i = 1094 := by omega
            subst i
            exact ok1094
      · by_cases h1095_1098 : i < 1096
        · have e : i = 1095 := by omega
          subst i
          exact ok1095
        · by_cases h1096_1098 : i < 1097
          · have e : i = 1096 := by omega
            subst i
            exact ok1096
          · have e : i = 1097 := by omega
            subst i
            exact ok1097
    · by_cases h1098_1104 : i < 1101
      · by_cases h1098_1101 : i < 1099
        · have e : i = 1098 := by omega
          subst i
          exact ok1098
        · by_cases h1099_1101 : i < 1100
          · have e : i = 1099 := by omega
            subst i
            exact ok1099
          · have e : i = 1100 := by omega
            subst i
            exact ok1100
      · by_cases h1101_1104 : i < 1102
        · have e : i = 1101 := by omega
          subst i
          exact ok1101
        · by_cases h1102_1104 : i < 1103
          · have e : i = 1102 := by omega
            subst i
            exact ok1102
          · have e : i = 1103 := by omega
            subst i
            exact ok1103
end HaarC5Data
