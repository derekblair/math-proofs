import HaarC5Data
namespace HaarC5Data
open HaarC5DAG HaarC5Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1104 : valid D 1104 := by decide +kernel
private theorem ok1105 : valid D 1105 := by decide +kernel
private theorem ok1106 : valid D 1106 := by decide +kernel
private theorem ok1107 : valid D 1107 := by decide +kernel
private theorem ok1108 : valid D 1108 := by decide +kernel
private theorem ok1109 : valid D 1109 := by decide +kernel
private theorem ok1110 : valid D 1110 := by decide +kernel
private theorem ok1111 : valid D 1111 := by decide +kernel
private theorem ok1112 : valid D 1112 := by decide +kernel
private theorem ok1113 : valid D 1113 := by decide +kernel
private theorem ok1114 : valid D 1114 := by decide +kernel
private theorem ok1115 : valid D 1115 := by decide +kernel
private theorem ok1116 : valid D 1116 := by decide +kernel
private theorem ok1117 : valid D 1117 := by decide +kernel
private theorem ok1118 : valid D 1118 := by decide +kernel
private theorem ok1119 : valid D 1119 := by decide +kernel
private theorem ok1120 : valid D 1120 := by decide +kernel
private theorem ok1121 : valid D 1121 := by decide +kernel
private theorem ok1122 : valid D 1122 := by decide +kernel
private theorem ok1123 : valid D 1123 := by decide +kernel
private theorem ok1124 : valid D 1124 := by decide +kernel
private theorem ok1125 : valid D 1125 := by decide +kernel
private theorem ok1126 : valid D 1126 := by decide +kernel
private theorem ok1127 : valid D 1127 := by decide +kernel
theorem C1104valid (i : Nat) (_lo : 1104 ≤ i) (_hi : i < 1128) : valid D i := by
  by_cases h1104_1128 : i < 1116
  · by_cases h1104_1116 : i < 1110
    · by_cases h1104_1110 : i < 1107
      · by_cases h1104_1107 : i < 1105
        · have e : i = 1104 := by omega
          subst i
          exact ok1104
        · by_cases h1105_1107 : i < 1106
          · have e : i = 1105 := by omega
            subst i
            exact ok1105
          · have e : i = 1106 := by omega
            subst i
            exact ok1106
      · by_cases h1107_1110 : i < 1108
        · have e : i = 1107 := by omega
          subst i
          exact ok1107
        · by_cases h1108_1110 : i < 1109
          · have e : i = 1108 := by omega
            subst i
            exact ok1108
          · have e : i = 1109 := by omega
            subst i
            exact ok1109
    · by_cases h1110_1116 : i < 1113
      · by_cases h1110_1113 : i < 1111
        · have e : i = 1110 := by omega
          subst i
          exact ok1110
        · by_cases h1111_1113 : i < 1112
          · have e : i = 1111 := by omega
            subst i
            exact ok1111
          · have e : i = 1112 := by omega
            subst i
            exact ok1112
      · by_cases h1113_1116 : i < 1114
        · have e : i = 1113 := by omega
          subst i
          exact ok1113
        · by_cases h1114_1116 : i < 1115
          · have e : i = 1114 := by omega
            subst i
            exact ok1114
          · have e : i = 1115 := by omega
            subst i
            exact ok1115
  · by_cases h1116_1128 : i < 1122
    · by_cases h1116_1122 : i < 1119
      · by_cases h1116_1119 : i < 1117
        · have e : i = 1116 := by omega
          subst i
          exact ok1116
        · by_cases h1117_1119 : i < 1118
          · have e : i = 1117 := by omega
            subst i
            exact ok1117
          · have e : i = 1118 := by omega
            subst i
            exact ok1118
      · by_cases h1119_1122 : i < 1120
        · have e : i = 1119 := by omega
          subst i
          exact ok1119
        · by_cases h1120_1122 : i < 1121
          · have e : i = 1120 := by omega
            subst i
            exact ok1120
          · have e : i = 1121 := by omega
            subst i
            exact ok1121
    · by_cases h1122_1128 : i < 1125
      · by_cases h1122_1125 : i < 1123
        · have e : i = 1122 := by omega
          subst i
          exact ok1122
        · by_cases h1123_1125 : i < 1124
          · have e : i = 1123 := by omega
            subst i
            exact ok1123
          · have e : i = 1124 := by omega
            subst i
            exact ok1124
      · by_cases h1125_1128 : i < 1126
        · have e : i = 1125 := by omega
          subst i
          exact ok1125
        · by_cases h1126_1128 : i < 1127
          · have e : i = 1126 := by omega
            subst i
            exact ok1126
          · have e : i = 1127 := by omega
            subst i
            exact ok1127
end HaarC5Data
