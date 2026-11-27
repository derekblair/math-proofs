import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1176 : valid D 1176 := by decide +kernel
private theorem ok1177 : valid D 1177 := by decide +kernel
private theorem ok1178 : valid D 1178 := by decide +kernel
private theorem ok1179 : valid D 1179 := by decide +kernel
private theorem ok1180 : valid D 1180 := by decide +kernel
private theorem ok1181 : valid D 1181 := by decide +kernel
private theorem ok1182 : valid D 1182 := by decide +kernel
private theorem ok1183 : valid D 1183 := by decide +kernel
private theorem ok1184 : valid D 1184 := by decide +kernel
private theorem ok1185 : valid D 1185 := by decide +kernel
private theorem ok1186 : valid D 1186 := by decide +kernel
private theorem ok1187 : valid D 1187 := by decide +kernel
private theorem ok1188 : valid D 1188 := by decide +kernel
private theorem ok1189 : valid D 1189 := by decide +kernel
private theorem ok1190 : valid D 1190 := by decide +kernel
private theorem ok1191 : valid D 1191 := by decide +kernel
private theorem ok1192 : valid D 1192 := by decide +kernel
private theorem ok1193 : valid D 1193 := by decide +kernel
private theorem ok1194 : valid D 1194 := by decide +kernel
private theorem ok1195 : valid D 1195 := by decide +kernel
private theorem ok1196 : valid D 1196 := by decide +kernel
private theorem ok1197 : valid D 1197 := by decide +kernel
private theorem ok1198 : valid D 1198 := by decide +kernel
private theorem ok1199 : valid D 1199 := by decide +kernel
theorem C1176valid (i : Nat) (_lo : 1176 ≤ i) (_hi : i < 1200) : valid D i := by
  by_cases h1176_1200 : i < 1188
  · by_cases h1176_1188 : i < 1182
    · by_cases h1176_1182 : i < 1179
      · by_cases h1176_1179 : i < 1177
        · have e : i = 1176 := by omega
          subst i
          exact ok1176
        · by_cases h1177_1179 : i < 1178
          · have e : i = 1177 := by omega
            subst i
            exact ok1177
          · have e : i = 1178 := by omega
            subst i
            exact ok1178
      · by_cases h1179_1182 : i < 1180
        · have e : i = 1179 := by omega
          subst i
          exact ok1179
        · by_cases h1180_1182 : i < 1181
          · have e : i = 1180 := by omega
            subst i
            exact ok1180
          · have e : i = 1181 := by omega
            subst i
            exact ok1181
    · by_cases h1182_1188 : i < 1185
      · by_cases h1182_1185 : i < 1183
        · have e : i = 1182 := by omega
          subst i
          exact ok1182
        · by_cases h1183_1185 : i < 1184
          · have e : i = 1183 := by omega
            subst i
            exact ok1183
          · have e : i = 1184 := by omega
            subst i
            exact ok1184
      · by_cases h1185_1188 : i < 1186
        · have e : i = 1185 := by omega
          subst i
          exact ok1185
        · by_cases h1186_1188 : i < 1187
          · have e : i = 1186 := by omega
            subst i
            exact ok1186
          · have e : i = 1187 := by omega
            subst i
            exact ok1187
  · by_cases h1188_1200 : i < 1194
    · by_cases h1188_1194 : i < 1191
      · by_cases h1188_1191 : i < 1189
        · have e : i = 1188 := by omega
          subst i
          exact ok1188
        · by_cases h1189_1191 : i < 1190
          · have e : i = 1189 := by omega
            subst i
            exact ok1189
          · have e : i = 1190 := by omega
            subst i
            exact ok1190
      · by_cases h1191_1194 : i < 1192
        · have e : i = 1191 := by omega
          subst i
          exact ok1191
        · by_cases h1192_1194 : i < 1193
          · have e : i = 1192 := by omega
            subst i
            exact ok1192
          · have e : i = 1193 := by omega
            subst i
            exact ok1193
    · by_cases h1194_1200 : i < 1197
      · by_cases h1194_1197 : i < 1195
        · have e : i = 1194 := by omega
          subst i
          exact ok1194
        · by_cases h1195_1197 : i < 1196
          · have e : i = 1195 := by omega
            subst i
            exact ok1195
          · have e : i = 1196 := by omega
            subst i
            exact ok1196
      · by_cases h1197_1200 : i < 1198
        · have e : i = 1197 := by omega
          subst i
          exact ok1197
        · by_cases h1198_1200 : i < 1199
          · have e : i = 1198 := by omega
            subst i
            exact ok1198
          · have e : i = 1199 := by omega
            subst i
            exact ok1199
end HaarHoneyData
