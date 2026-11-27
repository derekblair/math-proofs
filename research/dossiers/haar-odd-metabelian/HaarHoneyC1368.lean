import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1368 : valid D 1368 := by decide +kernel
private theorem ok1369 : valid D 1369 := by decide +kernel
private theorem ok1370 : valid D 1370 := by decide +kernel
private theorem ok1371 : valid D 1371 := by decide +kernel
private theorem ok1372 : valid D 1372 := by decide +kernel
private theorem ok1373 : valid D 1373 := by decide +kernel
private theorem ok1374 : valid D 1374 := by decide +kernel
private theorem ok1375 : valid D 1375 := by decide +kernel
private theorem ok1376 : valid D 1376 := by decide +kernel
private theorem ok1377 : valid D 1377 := by decide +kernel
private theorem ok1378 : valid D 1378 := by decide +kernel
private theorem ok1379 : valid D 1379 := by decide +kernel
private theorem ok1380 : valid D 1380 := by decide +kernel
private theorem ok1381 : valid D 1381 := by decide +kernel
private theorem ok1382 : valid D 1382 := by decide +kernel
private theorem ok1383 : valid D 1383 := by decide +kernel
private theorem ok1384 : valid D 1384 := by decide +kernel
private theorem ok1385 : valid D 1385 := by decide +kernel
private theorem ok1386 : valid D 1386 := by decide +kernel
private theorem ok1387 : valid D 1387 := by decide +kernel
private theorem ok1388 : valid D 1388 := by decide +kernel
private theorem ok1389 : valid D 1389 := by decide +kernel
private theorem ok1390 : valid D 1390 := by decide +kernel
private theorem ok1391 : valid D 1391 := by decide +kernel
theorem C1368valid (i : Nat) (_lo : 1368 ≤ i) (_hi : i < 1392) : valid D i := by
  by_cases h1368_1392 : i < 1380
  · by_cases h1368_1380 : i < 1374
    · by_cases h1368_1374 : i < 1371
      · by_cases h1368_1371 : i < 1369
        · have e : i = 1368 := by omega
          subst i
          exact ok1368
        · by_cases h1369_1371 : i < 1370
          · have e : i = 1369 := by omega
            subst i
            exact ok1369
          · have e : i = 1370 := by omega
            subst i
            exact ok1370
      · by_cases h1371_1374 : i < 1372
        · have e : i = 1371 := by omega
          subst i
          exact ok1371
        · by_cases h1372_1374 : i < 1373
          · have e : i = 1372 := by omega
            subst i
            exact ok1372
          · have e : i = 1373 := by omega
            subst i
            exact ok1373
    · by_cases h1374_1380 : i < 1377
      · by_cases h1374_1377 : i < 1375
        · have e : i = 1374 := by omega
          subst i
          exact ok1374
        · by_cases h1375_1377 : i < 1376
          · have e : i = 1375 := by omega
            subst i
            exact ok1375
          · have e : i = 1376 := by omega
            subst i
            exact ok1376
      · by_cases h1377_1380 : i < 1378
        · have e : i = 1377 := by omega
          subst i
          exact ok1377
        · by_cases h1378_1380 : i < 1379
          · have e : i = 1378 := by omega
            subst i
            exact ok1378
          · have e : i = 1379 := by omega
            subst i
            exact ok1379
  · by_cases h1380_1392 : i < 1386
    · by_cases h1380_1386 : i < 1383
      · by_cases h1380_1383 : i < 1381
        · have e : i = 1380 := by omega
          subst i
          exact ok1380
        · by_cases h1381_1383 : i < 1382
          · have e : i = 1381 := by omega
            subst i
            exact ok1381
          · have e : i = 1382 := by omega
            subst i
            exact ok1382
      · by_cases h1383_1386 : i < 1384
        · have e : i = 1383 := by omega
          subst i
          exact ok1383
        · by_cases h1384_1386 : i < 1385
          · have e : i = 1384 := by omega
            subst i
            exact ok1384
          · have e : i = 1385 := by omega
            subst i
            exact ok1385
    · by_cases h1386_1392 : i < 1389
      · by_cases h1386_1389 : i < 1387
        · have e : i = 1386 := by omega
          subst i
          exact ok1386
        · by_cases h1387_1389 : i < 1388
          · have e : i = 1387 := by omega
            subst i
            exact ok1387
          · have e : i = 1388 := by omega
            subst i
            exact ok1388
      · by_cases h1389_1392 : i < 1390
        · have e : i = 1389 := by omega
          subst i
          exact ok1389
        · by_cases h1390_1392 : i < 1391
          · have e : i = 1390 := by omega
            subst i
            exact ok1390
          · have e : i = 1391 := by omega
            subst i
            exact ok1391
end HaarHoneyData
