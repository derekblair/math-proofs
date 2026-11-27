import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1152 : valid D 1152 := by decide +kernel
private theorem ok1153 : valid D 1153 := by decide +kernel
private theorem ok1154 : valid D 1154 := by decide +kernel
private theorem ok1155 : valid D 1155 := by decide +kernel
private theorem ok1156 : valid D 1156 := by decide +kernel
private theorem ok1157 : valid D 1157 := by decide +kernel
private theorem ok1158 : valid D 1158 := by decide +kernel
private theorem ok1159 : valid D 1159 := by decide +kernel
private theorem ok1160 : valid D 1160 := by decide +kernel
private theorem ok1161 : valid D 1161 := by decide +kernel
private theorem ok1162 : valid D 1162 := by decide +kernel
private theorem ok1163 : valid D 1163 := by decide +kernel
private theorem ok1164 : valid D 1164 := by decide +kernel
private theorem ok1165 : valid D 1165 := by decide +kernel
private theorem ok1166 : valid D 1166 := by decide +kernel
private theorem ok1167 : valid D 1167 := by decide +kernel
private theorem ok1168 : valid D 1168 := by decide +kernel
private theorem ok1169 : valid D 1169 := by decide +kernel
private theorem ok1170 : valid D 1170 := by decide +kernel
private theorem ok1171 : valid D 1171 := by decide +kernel
private theorem ok1172 : valid D 1172 := by decide +kernel
private theorem ok1173 : valid D 1173 := by decide +kernel
private theorem ok1174 : valid D 1174 := by decide +kernel
private theorem ok1175 : valid D 1175 := by decide +kernel
theorem C1152valid (i : Nat) (_lo : 1152 ≤ i) (_hi : i < 1176) : valid D i := by
  by_cases h1152_1176 : i < 1164
  · by_cases h1152_1164 : i < 1158
    · by_cases h1152_1158 : i < 1155
      · by_cases h1152_1155 : i < 1153
        · have e : i = 1152 := by omega
          subst i
          exact ok1152
        · by_cases h1153_1155 : i < 1154
          · have e : i = 1153 := by omega
            subst i
            exact ok1153
          · have e : i = 1154 := by omega
            subst i
            exact ok1154
      · by_cases h1155_1158 : i < 1156
        · have e : i = 1155 := by omega
          subst i
          exact ok1155
        · by_cases h1156_1158 : i < 1157
          · have e : i = 1156 := by omega
            subst i
            exact ok1156
          · have e : i = 1157 := by omega
            subst i
            exact ok1157
    · by_cases h1158_1164 : i < 1161
      · by_cases h1158_1161 : i < 1159
        · have e : i = 1158 := by omega
          subst i
          exact ok1158
        · by_cases h1159_1161 : i < 1160
          · have e : i = 1159 := by omega
            subst i
            exact ok1159
          · have e : i = 1160 := by omega
            subst i
            exact ok1160
      · by_cases h1161_1164 : i < 1162
        · have e : i = 1161 := by omega
          subst i
          exact ok1161
        · by_cases h1162_1164 : i < 1163
          · have e : i = 1162 := by omega
            subst i
            exact ok1162
          · have e : i = 1163 := by omega
            subst i
            exact ok1163
  · by_cases h1164_1176 : i < 1170
    · by_cases h1164_1170 : i < 1167
      · by_cases h1164_1167 : i < 1165
        · have e : i = 1164 := by omega
          subst i
          exact ok1164
        · by_cases h1165_1167 : i < 1166
          · have e : i = 1165 := by omega
            subst i
            exact ok1165
          · have e : i = 1166 := by omega
            subst i
            exact ok1166
      · by_cases h1167_1170 : i < 1168
        · have e : i = 1167 := by omega
          subst i
          exact ok1167
        · by_cases h1168_1170 : i < 1169
          · have e : i = 1168 := by omega
            subst i
            exact ok1168
          · have e : i = 1169 := by omega
            subst i
            exact ok1169
    · by_cases h1170_1176 : i < 1173
      · by_cases h1170_1173 : i < 1171
        · have e : i = 1170 := by omega
          subst i
          exact ok1170
        · by_cases h1171_1173 : i < 1172
          · have e : i = 1171 := by omega
            subst i
            exact ok1171
          · have e : i = 1172 := by omega
            subst i
            exact ok1172
      · by_cases h1173_1176 : i < 1174
        · have e : i = 1173 := by omega
          subst i
          exact ok1173
        · by_cases h1174_1176 : i < 1175
          · have e : i = 1174 := by omega
            subst i
            exact ok1174
          · have e : i = 1175 := by omega
            subst i
            exact ok1175
end HaarHoneyData
