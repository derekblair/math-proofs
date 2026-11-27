import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1344 : valid D 1344 := by decide +kernel
private theorem ok1345 : valid D 1345 := by decide +kernel
private theorem ok1346 : valid D 1346 := by decide +kernel
private theorem ok1347 : valid D 1347 := by decide +kernel
private theorem ok1348 : valid D 1348 := by decide +kernel
private theorem ok1349 : valid D 1349 := by decide +kernel
private theorem ok1350 : valid D 1350 := by decide +kernel
private theorem ok1351 : valid D 1351 := by decide +kernel
private theorem ok1352 : valid D 1352 := by decide +kernel
private theorem ok1353 : valid D 1353 := by decide +kernel
private theorem ok1354 : valid D 1354 := by decide +kernel
private theorem ok1355 : valid D 1355 := by decide +kernel
private theorem ok1356 : valid D 1356 := by decide +kernel
private theorem ok1357 : valid D 1357 := by decide +kernel
private theorem ok1358 : valid D 1358 := by decide +kernel
private theorem ok1359 : valid D 1359 := by decide +kernel
private theorem ok1360 : valid D 1360 := by decide +kernel
private theorem ok1361 : valid D 1361 := by decide +kernel
private theorem ok1362 : valid D 1362 := by decide +kernel
private theorem ok1363 : valid D 1363 := by decide +kernel
private theorem ok1364 : valid D 1364 := by decide +kernel
private theorem ok1365 : valid D 1365 := by decide +kernel
private theorem ok1366 : valid D 1366 := by decide +kernel
private theorem ok1367 : valid D 1367 := by decide +kernel
theorem C1344valid (i : Nat) (_lo : 1344 ≤ i) (_hi : i < 1368) : valid D i := by
  by_cases h1344_1368 : i < 1356
  · by_cases h1344_1356 : i < 1350
    · by_cases h1344_1350 : i < 1347
      · by_cases h1344_1347 : i < 1345
        · have e : i = 1344 := by omega
          subst i
          exact ok1344
        · by_cases h1345_1347 : i < 1346
          · have e : i = 1345 := by omega
            subst i
            exact ok1345
          · have e : i = 1346 := by omega
            subst i
            exact ok1346
      · by_cases h1347_1350 : i < 1348
        · have e : i = 1347 := by omega
          subst i
          exact ok1347
        · by_cases h1348_1350 : i < 1349
          · have e : i = 1348 := by omega
            subst i
            exact ok1348
          · have e : i = 1349 := by omega
            subst i
            exact ok1349
    · by_cases h1350_1356 : i < 1353
      · by_cases h1350_1353 : i < 1351
        · have e : i = 1350 := by omega
          subst i
          exact ok1350
        · by_cases h1351_1353 : i < 1352
          · have e : i = 1351 := by omega
            subst i
            exact ok1351
          · have e : i = 1352 := by omega
            subst i
            exact ok1352
      · by_cases h1353_1356 : i < 1354
        · have e : i = 1353 := by omega
          subst i
          exact ok1353
        · by_cases h1354_1356 : i < 1355
          · have e : i = 1354 := by omega
            subst i
            exact ok1354
          · have e : i = 1355 := by omega
            subst i
            exact ok1355
  · by_cases h1356_1368 : i < 1362
    · by_cases h1356_1362 : i < 1359
      · by_cases h1356_1359 : i < 1357
        · have e : i = 1356 := by omega
          subst i
          exact ok1356
        · by_cases h1357_1359 : i < 1358
          · have e : i = 1357 := by omega
            subst i
            exact ok1357
          · have e : i = 1358 := by omega
            subst i
            exact ok1358
      · by_cases h1359_1362 : i < 1360
        · have e : i = 1359 := by omega
          subst i
          exact ok1359
        · by_cases h1360_1362 : i < 1361
          · have e : i = 1360 := by omega
            subst i
            exact ok1360
          · have e : i = 1361 := by omega
            subst i
            exact ok1361
    · by_cases h1362_1368 : i < 1365
      · by_cases h1362_1365 : i < 1363
        · have e : i = 1362 := by omega
          subst i
          exact ok1362
        · by_cases h1363_1365 : i < 1364
          · have e : i = 1363 := by omega
            subst i
            exact ok1363
          · have e : i = 1364 := by omega
            subst i
            exact ok1364
      · by_cases h1365_1368 : i < 1366
        · have e : i = 1365 := by omega
          subst i
          exact ok1365
        · by_cases h1366_1368 : i < 1367
          · have e : i = 1366 := by omega
            subst i
            exact ok1366
          · have e : i = 1367 := by omega
            subst i
            exact ok1367
end HaarHoneyData
