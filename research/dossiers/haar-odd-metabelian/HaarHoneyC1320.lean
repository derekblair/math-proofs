import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1320 : valid D 1320 := by decide +kernel
private theorem ok1321 : valid D 1321 := by decide +kernel
private theorem ok1322 : valid D 1322 := by decide +kernel
private theorem ok1323 : valid D 1323 := by decide +kernel
private theorem ok1324 : valid D 1324 := by decide +kernel
private theorem ok1325 : valid D 1325 := by decide +kernel
private theorem ok1326 : valid D 1326 := by decide +kernel
private theorem ok1327 : valid D 1327 := by decide +kernel
private theorem ok1328 : valid D 1328 := by decide +kernel
private theorem ok1329 : valid D 1329 := by decide +kernel
private theorem ok1330 : valid D 1330 := by decide +kernel
private theorem ok1331 : valid D 1331 := by decide +kernel
private theorem ok1332 : valid D 1332 := by decide +kernel
private theorem ok1333 : valid D 1333 := by decide +kernel
private theorem ok1334 : valid D 1334 := by decide +kernel
private theorem ok1335 : valid D 1335 := by decide +kernel
private theorem ok1336 : valid D 1336 := by decide +kernel
private theorem ok1337 : valid D 1337 := by decide +kernel
private theorem ok1338 : valid D 1338 := by decide +kernel
private theorem ok1339 : valid D 1339 := by decide +kernel
private theorem ok1340 : valid D 1340 := by decide +kernel
private theorem ok1341 : valid D 1341 := by decide +kernel
private theorem ok1342 : valid D 1342 := by decide +kernel
private theorem ok1343 : valid D 1343 := by decide +kernel
theorem C1320valid (i : Nat) (_lo : 1320 ≤ i) (_hi : i < 1344) : valid D i := by
  by_cases h1320_1344 : i < 1332
  · by_cases h1320_1332 : i < 1326
    · by_cases h1320_1326 : i < 1323
      · by_cases h1320_1323 : i < 1321
        · have e : i = 1320 := by omega
          subst i
          exact ok1320
        · by_cases h1321_1323 : i < 1322
          · have e : i = 1321 := by omega
            subst i
            exact ok1321
          · have e : i = 1322 := by omega
            subst i
            exact ok1322
      · by_cases h1323_1326 : i < 1324
        · have e : i = 1323 := by omega
          subst i
          exact ok1323
        · by_cases h1324_1326 : i < 1325
          · have e : i = 1324 := by omega
            subst i
            exact ok1324
          · have e : i = 1325 := by omega
            subst i
            exact ok1325
    · by_cases h1326_1332 : i < 1329
      · by_cases h1326_1329 : i < 1327
        · have e : i = 1326 := by omega
          subst i
          exact ok1326
        · by_cases h1327_1329 : i < 1328
          · have e : i = 1327 := by omega
            subst i
            exact ok1327
          · have e : i = 1328 := by omega
            subst i
            exact ok1328
      · by_cases h1329_1332 : i < 1330
        · have e : i = 1329 := by omega
          subst i
          exact ok1329
        · by_cases h1330_1332 : i < 1331
          · have e : i = 1330 := by omega
            subst i
            exact ok1330
          · have e : i = 1331 := by omega
            subst i
            exact ok1331
  · by_cases h1332_1344 : i < 1338
    · by_cases h1332_1338 : i < 1335
      · by_cases h1332_1335 : i < 1333
        · have e : i = 1332 := by omega
          subst i
          exact ok1332
        · by_cases h1333_1335 : i < 1334
          · have e : i = 1333 := by omega
            subst i
            exact ok1333
          · have e : i = 1334 := by omega
            subst i
            exact ok1334
      · by_cases h1335_1338 : i < 1336
        · have e : i = 1335 := by omega
          subst i
          exact ok1335
        · by_cases h1336_1338 : i < 1337
          · have e : i = 1336 := by omega
            subst i
            exact ok1336
          · have e : i = 1337 := by omega
            subst i
            exact ok1337
    · by_cases h1338_1344 : i < 1341
      · by_cases h1338_1341 : i < 1339
        · have e : i = 1338 := by omega
          subst i
          exact ok1338
        · by_cases h1339_1341 : i < 1340
          · have e : i = 1339 := by omega
            subst i
            exact ok1339
          · have e : i = 1340 := by omega
            subst i
            exact ok1340
      · by_cases h1341_1344 : i < 1342
        · have e : i = 1341 := by omega
          subst i
          exact ok1341
        · by_cases h1342_1344 : i < 1343
          · have e : i = 1342 := by omega
            subst i
            exact ok1342
          · have e : i = 1343 := by omega
            subst i
            exact ok1343
end HaarHoneyData
