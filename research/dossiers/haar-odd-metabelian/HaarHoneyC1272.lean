import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1272 : valid D 1272 := by decide +kernel
private theorem ok1273 : valid D 1273 := by decide +kernel
private theorem ok1274 : valid D 1274 := by decide +kernel
private theorem ok1275 : valid D 1275 := by decide +kernel
private theorem ok1276 : valid D 1276 := by decide +kernel
private theorem ok1277 : valid D 1277 := by decide +kernel
private theorem ok1278 : valid D 1278 := by decide +kernel
private theorem ok1279 : valid D 1279 := by decide +kernel
private theorem ok1280 : valid D 1280 := by decide +kernel
private theorem ok1281 : valid D 1281 := by decide +kernel
private theorem ok1282 : valid D 1282 := by decide +kernel
private theorem ok1283 : valid D 1283 := by decide +kernel
private theorem ok1284 : valid D 1284 := by decide +kernel
private theorem ok1285 : valid D 1285 := by decide +kernel
private theorem ok1286 : valid D 1286 := by decide +kernel
private theorem ok1287 : valid D 1287 := by decide +kernel
private theorem ok1288 : valid D 1288 := by decide +kernel
private theorem ok1289 : valid D 1289 := by decide +kernel
private theorem ok1290 : valid D 1290 := by decide +kernel
private theorem ok1291 : valid D 1291 := by decide +kernel
private theorem ok1292 : valid D 1292 := by decide +kernel
private theorem ok1293 : valid D 1293 := by decide +kernel
private theorem ok1294 : valid D 1294 := by decide +kernel
private theorem ok1295 : valid D 1295 := by decide +kernel
theorem C1272valid (i : Nat) (_lo : 1272 ≤ i) (_hi : i < 1296) : valid D i := by
  by_cases h1272_1296 : i < 1284
  · by_cases h1272_1284 : i < 1278
    · by_cases h1272_1278 : i < 1275
      · by_cases h1272_1275 : i < 1273
        · have e : i = 1272 := by omega
          subst i
          exact ok1272
        · by_cases h1273_1275 : i < 1274
          · have e : i = 1273 := by omega
            subst i
            exact ok1273
          · have e : i = 1274 := by omega
            subst i
            exact ok1274
      · by_cases h1275_1278 : i < 1276
        · have e : i = 1275 := by omega
          subst i
          exact ok1275
        · by_cases h1276_1278 : i < 1277
          · have e : i = 1276 := by omega
            subst i
            exact ok1276
          · have e : i = 1277 := by omega
            subst i
            exact ok1277
    · by_cases h1278_1284 : i < 1281
      · by_cases h1278_1281 : i < 1279
        · have e : i = 1278 := by omega
          subst i
          exact ok1278
        · by_cases h1279_1281 : i < 1280
          · have e : i = 1279 := by omega
            subst i
            exact ok1279
          · have e : i = 1280 := by omega
            subst i
            exact ok1280
      · by_cases h1281_1284 : i < 1282
        · have e : i = 1281 := by omega
          subst i
          exact ok1281
        · by_cases h1282_1284 : i < 1283
          · have e : i = 1282 := by omega
            subst i
            exact ok1282
          · have e : i = 1283 := by omega
            subst i
            exact ok1283
  · by_cases h1284_1296 : i < 1290
    · by_cases h1284_1290 : i < 1287
      · by_cases h1284_1287 : i < 1285
        · have e : i = 1284 := by omega
          subst i
          exact ok1284
        · by_cases h1285_1287 : i < 1286
          · have e : i = 1285 := by omega
            subst i
            exact ok1285
          · have e : i = 1286 := by omega
            subst i
            exact ok1286
      · by_cases h1287_1290 : i < 1288
        · have e : i = 1287 := by omega
          subst i
          exact ok1287
        · by_cases h1288_1290 : i < 1289
          · have e : i = 1288 := by omega
            subst i
            exact ok1288
          · have e : i = 1289 := by omega
            subst i
            exact ok1289
    · by_cases h1290_1296 : i < 1293
      · by_cases h1290_1293 : i < 1291
        · have e : i = 1290 := by omega
          subst i
          exact ok1290
        · by_cases h1291_1293 : i < 1292
          · have e : i = 1291 := by omega
            subst i
            exact ok1291
          · have e : i = 1292 := by omega
            subst i
            exact ok1292
      · by_cases h1293_1296 : i < 1294
        · have e : i = 1293 := by omega
          subst i
          exact ok1293
        · by_cases h1294_1296 : i < 1295
          · have e : i = 1294 := by omega
            subst i
            exact ok1294
          · have e : i = 1295 := by omega
            subst i
            exact ok1295
end HaarHoneyData
