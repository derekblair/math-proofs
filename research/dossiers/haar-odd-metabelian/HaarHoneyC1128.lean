import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1128 : valid D 1128 := by decide +kernel
private theorem ok1129 : valid D 1129 := by decide +kernel
private theorem ok1130 : valid D 1130 := by decide +kernel
private theorem ok1131 : valid D 1131 := by decide +kernel
private theorem ok1132 : valid D 1132 := by decide +kernel
private theorem ok1133 : valid D 1133 := by decide +kernel
private theorem ok1134 : valid D 1134 := by decide +kernel
private theorem ok1135 : valid D 1135 := by decide +kernel
private theorem ok1136 : valid D 1136 := by decide +kernel
private theorem ok1137 : valid D 1137 := by decide +kernel
private theorem ok1138 : valid D 1138 := by decide +kernel
private theorem ok1139 : valid D 1139 := by decide +kernel
private theorem ok1140 : valid D 1140 := by decide +kernel
private theorem ok1141 : valid D 1141 := by decide +kernel
private theorem ok1142 : valid D 1142 := by decide +kernel
private theorem ok1143 : valid D 1143 := by decide +kernel
private theorem ok1144 : valid D 1144 := by decide +kernel
private theorem ok1145 : valid D 1145 := by decide +kernel
private theorem ok1146 : valid D 1146 := by decide +kernel
private theorem ok1147 : valid D 1147 := by decide +kernel
private theorem ok1148 : valid D 1148 := by decide +kernel
private theorem ok1149 : valid D 1149 := by decide +kernel
private theorem ok1150 : valid D 1150 := by decide +kernel
private theorem ok1151 : valid D 1151 := by decide +kernel
theorem C1128valid (i : Nat) (_lo : 1128 ≤ i) (_hi : i < 1152) : valid D i := by
  by_cases h1128_1152 : i < 1140
  · by_cases h1128_1140 : i < 1134
    · by_cases h1128_1134 : i < 1131
      · by_cases h1128_1131 : i < 1129
        · have e : i = 1128 := by omega
          subst i
          exact ok1128
        · by_cases h1129_1131 : i < 1130
          · have e : i = 1129 := by omega
            subst i
            exact ok1129
          · have e : i = 1130 := by omega
            subst i
            exact ok1130
      · by_cases h1131_1134 : i < 1132
        · have e : i = 1131 := by omega
          subst i
          exact ok1131
        · by_cases h1132_1134 : i < 1133
          · have e : i = 1132 := by omega
            subst i
            exact ok1132
          · have e : i = 1133 := by omega
            subst i
            exact ok1133
    · by_cases h1134_1140 : i < 1137
      · by_cases h1134_1137 : i < 1135
        · have e : i = 1134 := by omega
          subst i
          exact ok1134
        · by_cases h1135_1137 : i < 1136
          · have e : i = 1135 := by omega
            subst i
            exact ok1135
          · have e : i = 1136 := by omega
            subst i
            exact ok1136
      · by_cases h1137_1140 : i < 1138
        · have e : i = 1137 := by omega
          subst i
          exact ok1137
        · by_cases h1138_1140 : i < 1139
          · have e : i = 1138 := by omega
            subst i
            exact ok1138
          · have e : i = 1139 := by omega
            subst i
            exact ok1139
  · by_cases h1140_1152 : i < 1146
    · by_cases h1140_1146 : i < 1143
      · by_cases h1140_1143 : i < 1141
        · have e : i = 1140 := by omega
          subst i
          exact ok1140
        · by_cases h1141_1143 : i < 1142
          · have e : i = 1141 := by omega
            subst i
            exact ok1141
          · have e : i = 1142 := by omega
            subst i
            exact ok1142
      · by_cases h1143_1146 : i < 1144
        · have e : i = 1143 := by omega
          subst i
          exact ok1143
        · by_cases h1144_1146 : i < 1145
          · have e : i = 1144 := by omega
            subst i
            exact ok1144
          · have e : i = 1145 := by omega
            subst i
            exact ok1145
    · by_cases h1146_1152 : i < 1149
      · by_cases h1146_1149 : i < 1147
        · have e : i = 1146 := by omega
          subst i
          exact ok1146
        · by_cases h1147_1149 : i < 1148
          · have e : i = 1147 := by omega
            subst i
            exact ok1147
          · have e : i = 1148 := by omega
            subst i
            exact ok1148
      · by_cases h1149_1152 : i < 1150
        · have e : i = 1149 := by omega
          subst i
          exact ok1149
        · by_cases h1150_1152 : i < 1151
          · have e : i = 1150 := by omega
            subst i
            exact ok1150
          · have e : i = 1151 := by omega
            subst i
            exact ok1151
end HaarHoneyData
