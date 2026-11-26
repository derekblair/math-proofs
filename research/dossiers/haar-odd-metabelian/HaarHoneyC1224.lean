import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1224 : valid D 1224 := by decide +kernel
private theorem ok1225 : valid D 1225 := by decide +kernel
private theorem ok1226 : valid D 1226 := by decide +kernel
private theorem ok1227 : valid D 1227 := by decide +kernel
private theorem ok1228 : valid D 1228 := by decide +kernel
private theorem ok1229 : valid D 1229 := by decide +kernel
private theorem ok1230 : valid D 1230 := by decide +kernel
private theorem ok1231 : valid D 1231 := by decide +kernel
private theorem ok1232 : valid D 1232 := by decide +kernel
private theorem ok1233 : valid D 1233 := by decide +kernel
private theorem ok1234 : valid D 1234 := by decide +kernel
private theorem ok1235 : valid D 1235 := by decide +kernel
private theorem ok1236 : valid D 1236 := by decide +kernel
private theorem ok1237 : valid D 1237 := by decide +kernel
private theorem ok1238 : valid D 1238 := by decide +kernel
private theorem ok1239 : valid D 1239 := by decide +kernel
private theorem ok1240 : valid D 1240 := by decide +kernel
private theorem ok1241 : valid D 1241 := by decide +kernel
private theorem ok1242 : valid D 1242 := by decide +kernel
private theorem ok1243 : valid D 1243 := by decide +kernel
private theorem ok1244 : valid D 1244 := by decide +kernel
private theorem ok1245 : valid D 1245 := by decide +kernel
private theorem ok1246 : valid D 1246 := by decide +kernel
private theorem ok1247 : valid D 1247 := by decide +kernel
theorem C1224valid (i : Nat) (_lo : 1224 ≤ i) (_hi : i < 1248) : valid D i := by
  by_cases h1224_1248 : i < 1236
  · by_cases h1224_1236 : i < 1230
    · by_cases h1224_1230 : i < 1227
      · by_cases h1224_1227 : i < 1225
        · have e : i = 1224 := by omega
          subst i
          exact ok1224
        · by_cases h1225_1227 : i < 1226
          · have e : i = 1225 := by omega
            subst i
            exact ok1225
          · have e : i = 1226 := by omega
            subst i
            exact ok1226
      · by_cases h1227_1230 : i < 1228
        · have e : i = 1227 := by omega
          subst i
          exact ok1227
        · by_cases h1228_1230 : i < 1229
          · have e : i = 1228 := by omega
            subst i
            exact ok1228
          · have e : i = 1229 := by omega
            subst i
            exact ok1229
    · by_cases h1230_1236 : i < 1233
      · by_cases h1230_1233 : i < 1231
        · have e : i = 1230 := by omega
          subst i
          exact ok1230
        · by_cases h1231_1233 : i < 1232
          · have e : i = 1231 := by omega
            subst i
            exact ok1231
          · have e : i = 1232 := by omega
            subst i
            exact ok1232
      · by_cases h1233_1236 : i < 1234
        · have e : i = 1233 := by omega
          subst i
          exact ok1233
        · by_cases h1234_1236 : i < 1235
          · have e : i = 1234 := by omega
            subst i
            exact ok1234
          · have e : i = 1235 := by omega
            subst i
            exact ok1235
  · by_cases h1236_1248 : i < 1242
    · by_cases h1236_1242 : i < 1239
      · by_cases h1236_1239 : i < 1237
        · have e : i = 1236 := by omega
          subst i
          exact ok1236
        · by_cases h1237_1239 : i < 1238
          · have e : i = 1237 := by omega
            subst i
            exact ok1237
          · have e : i = 1238 := by omega
            subst i
            exact ok1238
      · by_cases h1239_1242 : i < 1240
        · have e : i = 1239 := by omega
          subst i
          exact ok1239
        · by_cases h1240_1242 : i < 1241
          · have e : i = 1240 := by omega
            subst i
            exact ok1240
          · have e : i = 1241 := by omega
            subst i
            exact ok1241
    · by_cases h1242_1248 : i < 1245
      · by_cases h1242_1245 : i < 1243
        · have e : i = 1242 := by omega
          subst i
          exact ok1242
        · by_cases h1243_1245 : i < 1244
          · have e : i = 1243 := by omega
            subst i
            exact ok1243
          · have e : i = 1244 := by omega
            subst i
            exact ok1244
      · by_cases h1245_1248 : i < 1246
        · have e : i = 1245 := by omega
          subst i
          exact ok1245
        · by_cases h1246_1248 : i < 1247
          · have e : i = 1246 := by omega
            subst i
            exact ok1246
          · have e : i = 1247 := by omega
            subst i
            exact ok1247
end HaarHoneyData
