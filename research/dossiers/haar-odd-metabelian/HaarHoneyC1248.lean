import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1248 : valid D 1248 := by decide +kernel
private theorem ok1249 : valid D 1249 := by decide +kernel
private theorem ok1250 : valid D 1250 := by decide +kernel
private theorem ok1251 : valid D 1251 := by decide +kernel
private theorem ok1252 : valid D 1252 := by decide +kernel
private theorem ok1253 : valid D 1253 := by decide +kernel
private theorem ok1254 : valid D 1254 := by decide +kernel
private theorem ok1255 : valid D 1255 := by decide +kernel
private theorem ok1256 : valid D 1256 := by decide +kernel
private theorem ok1257 : valid D 1257 := by decide +kernel
private theorem ok1258 : valid D 1258 := by decide +kernel
private theorem ok1259 : valid D 1259 := by decide +kernel
private theorem ok1260 : valid D 1260 := by decide +kernel
private theorem ok1261 : valid D 1261 := by decide +kernel
private theorem ok1262 : valid D 1262 := by decide +kernel
private theorem ok1263 : valid D 1263 := by decide +kernel
private theorem ok1264 : valid D 1264 := by decide +kernel
private theorem ok1265 : valid D 1265 := by decide +kernel
private theorem ok1266 : valid D 1266 := by decide +kernel
private theorem ok1267 : valid D 1267 := by decide +kernel
private theorem ok1268 : valid D 1268 := by decide +kernel
private theorem ok1269 : valid D 1269 := by decide +kernel
private theorem ok1270 : valid D 1270 := by decide +kernel
private theorem ok1271 : valid D 1271 := by decide +kernel
theorem C1248valid (i : Nat) (_lo : 1248 ≤ i) (_hi : i < 1272) : valid D i := by
  by_cases h1248_1272 : i < 1260
  · by_cases h1248_1260 : i < 1254
    · by_cases h1248_1254 : i < 1251
      · by_cases h1248_1251 : i < 1249
        · have e : i = 1248 := by omega
          subst i
          exact ok1248
        · by_cases h1249_1251 : i < 1250
          · have e : i = 1249 := by omega
            subst i
            exact ok1249
          · have e : i = 1250 := by omega
            subst i
            exact ok1250
      · by_cases h1251_1254 : i < 1252
        · have e : i = 1251 := by omega
          subst i
          exact ok1251
        · by_cases h1252_1254 : i < 1253
          · have e : i = 1252 := by omega
            subst i
            exact ok1252
          · have e : i = 1253 := by omega
            subst i
            exact ok1253
    · by_cases h1254_1260 : i < 1257
      · by_cases h1254_1257 : i < 1255
        · have e : i = 1254 := by omega
          subst i
          exact ok1254
        · by_cases h1255_1257 : i < 1256
          · have e : i = 1255 := by omega
            subst i
            exact ok1255
          · have e : i = 1256 := by omega
            subst i
            exact ok1256
      · by_cases h1257_1260 : i < 1258
        · have e : i = 1257 := by omega
          subst i
          exact ok1257
        · by_cases h1258_1260 : i < 1259
          · have e : i = 1258 := by omega
            subst i
            exact ok1258
          · have e : i = 1259 := by omega
            subst i
            exact ok1259
  · by_cases h1260_1272 : i < 1266
    · by_cases h1260_1266 : i < 1263
      · by_cases h1260_1263 : i < 1261
        · have e : i = 1260 := by omega
          subst i
          exact ok1260
        · by_cases h1261_1263 : i < 1262
          · have e : i = 1261 := by omega
            subst i
            exact ok1261
          · have e : i = 1262 := by omega
            subst i
            exact ok1262
      · by_cases h1263_1266 : i < 1264
        · have e : i = 1263 := by omega
          subst i
          exact ok1263
        · by_cases h1264_1266 : i < 1265
          · have e : i = 1264 := by omega
            subst i
            exact ok1264
          · have e : i = 1265 := by omega
            subst i
            exact ok1265
    · by_cases h1266_1272 : i < 1269
      · by_cases h1266_1269 : i < 1267
        · have e : i = 1266 := by omega
          subst i
          exact ok1266
        · by_cases h1267_1269 : i < 1268
          · have e : i = 1267 := by omega
            subst i
            exact ok1267
          · have e : i = 1268 := by omega
            subst i
            exact ok1268
      · by_cases h1269_1272 : i < 1270
        · have e : i = 1269 := by omega
          subst i
          exact ok1269
        · by_cases h1270_1272 : i < 1271
          · have e : i = 1270 := by omega
            subst i
            exact ok1270
          · have e : i = 1271 := by omega
            subst i
            exact ok1271
end HaarHoneyData
