import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1200 : valid D 1200 := by decide +kernel
private theorem ok1201 : valid D 1201 := by decide +kernel
private theorem ok1202 : valid D 1202 := by decide +kernel
private theorem ok1203 : valid D 1203 := by decide +kernel
private theorem ok1204 : valid D 1204 := by decide +kernel
private theorem ok1205 : valid D 1205 := by decide +kernel
private theorem ok1206 : valid D 1206 := by decide +kernel
private theorem ok1207 : valid D 1207 := by decide +kernel
private theorem ok1208 : valid D 1208 := by decide +kernel
private theorem ok1209 : valid D 1209 := by decide +kernel
private theorem ok1210 : valid D 1210 := by decide +kernel
private theorem ok1211 : valid D 1211 := by decide +kernel
private theorem ok1212 : valid D 1212 := by decide +kernel
private theorem ok1213 : valid D 1213 := by decide +kernel
private theorem ok1214 : valid D 1214 := by decide +kernel
private theorem ok1215 : valid D 1215 := by decide +kernel
private theorem ok1216 : valid D 1216 := by decide +kernel
private theorem ok1217 : valid D 1217 := by decide +kernel
private theorem ok1218 : valid D 1218 := by decide +kernel
private theorem ok1219 : valid D 1219 := by decide +kernel
private theorem ok1220 : valid D 1220 := by decide +kernel
private theorem ok1221 : valid D 1221 := by decide +kernel
private theorem ok1222 : valid D 1222 := by decide +kernel
private theorem ok1223 : valid D 1223 := by decide +kernel
theorem C1200valid (i : Nat) (_lo : 1200 ≤ i) (_hi : i < 1224) : valid D i := by
  by_cases h1200_1224 : i < 1212
  · by_cases h1200_1212 : i < 1206
    · by_cases h1200_1206 : i < 1203
      · by_cases h1200_1203 : i < 1201
        · have e : i = 1200 := by omega
          subst i
          exact ok1200
        · by_cases h1201_1203 : i < 1202
          · have e : i = 1201 := by omega
            subst i
            exact ok1201
          · have e : i = 1202 := by omega
            subst i
            exact ok1202
      · by_cases h1203_1206 : i < 1204
        · have e : i = 1203 := by omega
          subst i
          exact ok1203
        · by_cases h1204_1206 : i < 1205
          · have e : i = 1204 := by omega
            subst i
            exact ok1204
          · have e : i = 1205 := by omega
            subst i
            exact ok1205
    · by_cases h1206_1212 : i < 1209
      · by_cases h1206_1209 : i < 1207
        · have e : i = 1206 := by omega
          subst i
          exact ok1206
        · by_cases h1207_1209 : i < 1208
          · have e : i = 1207 := by omega
            subst i
            exact ok1207
          · have e : i = 1208 := by omega
            subst i
            exact ok1208
      · by_cases h1209_1212 : i < 1210
        · have e : i = 1209 := by omega
          subst i
          exact ok1209
        · by_cases h1210_1212 : i < 1211
          · have e : i = 1210 := by omega
            subst i
            exact ok1210
          · have e : i = 1211 := by omega
            subst i
            exact ok1211
  · by_cases h1212_1224 : i < 1218
    · by_cases h1212_1218 : i < 1215
      · by_cases h1212_1215 : i < 1213
        · have e : i = 1212 := by omega
          subst i
          exact ok1212
        · by_cases h1213_1215 : i < 1214
          · have e : i = 1213 := by omega
            subst i
            exact ok1213
          · have e : i = 1214 := by omega
            subst i
            exact ok1214
      · by_cases h1215_1218 : i < 1216
        · have e : i = 1215 := by omega
          subst i
          exact ok1215
        · by_cases h1216_1218 : i < 1217
          · have e : i = 1216 := by omega
            subst i
            exact ok1216
          · have e : i = 1217 := by omega
            subst i
            exact ok1217
    · by_cases h1218_1224 : i < 1221
      · by_cases h1218_1221 : i < 1219
        · have e : i = 1218 := by omega
          subst i
          exact ok1218
        · by_cases h1219_1221 : i < 1220
          · have e : i = 1219 := by omega
            subst i
            exact ok1219
          · have e : i = 1220 := by omega
            subst i
            exact ok1220
      · by_cases h1221_1224 : i < 1222
        · have e : i = 1221 := by omega
          subst i
          exact ok1221
        · by_cases h1222_1224 : i < 1223
          · have e : i = 1222 := by omega
            subst i
            exact ok1222
          · have e : i = 1223 := by omega
            subst i
            exact ok1223
end HaarHoneyData
