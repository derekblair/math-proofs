import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1392 : valid D 1392 := by decide +kernel
private theorem ok1393 : valid D 1393 := by decide +kernel
private theorem ok1394 : valid D 1394 := by decide +kernel
private theorem ok1395 : valid D 1395 := by decide +kernel
private theorem ok1396 : valid D 1396 := by decide +kernel
private theorem ok1397 : valid D 1397 := by decide +kernel
private theorem ok1398 : valid D 1398 := by decide +kernel
private theorem ok1399 : valid D 1399 := by decide +kernel
private theorem ok1400 : valid D 1400 := by decide +kernel
private theorem ok1401 : valid D 1401 := by decide +kernel
private theorem ok1402 : valid D 1402 := by decide +kernel
private theorem ok1403 : valid D 1403 := by decide +kernel
private theorem ok1404 : valid D 1404 := by decide +kernel
private theorem ok1405 : valid D 1405 := by decide +kernel
private theorem ok1406 : valid D 1406 := by decide +kernel
private theorem ok1407 : valid D 1407 := by decide +kernel
private theorem ok1408 : valid D 1408 := by decide +kernel
private theorem ok1409 : valid D 1409 := by decide +kernel
private theorem ok1410 : valid D 1410 := by decide +kernel
private theorem ok1411 : valid D 1411 := by decide +kernel
private theorem ok1412 : valid D 1412 := by decide +kernel
private theorem ok1413 : valid D 1413 := by decide +kernel
private theorem ok1414 : valid D 1414 := by decide +kernel
private theorem ok1415 : valid D 1415 := by decide +kernel
theorem C1392valid (i : Nat) (_lo : 1392 ≤ i) (_hi : i < 1416) : valid D i := by
  by_cases h1392_1416 : i < 1404
  · by_cases h1392_1404 : i < 1398
    · by_cases h1392_1398 : i < 1395
      · by_cases h1392_1395 : i < 1393
        · have e : i = 1392 := by omega
          subst i
          exact ok1392
        · by_cases h1393_1395 : i < 1394
          · have e : i = 1393 := by omega
            subst i
            exact ok1393
          · have e : i = 1394 := by omega
            subst i
            exact ok1394
      · by_cases h1395_1398 : i < 1396
        · have e : i = 1395 := by omega
          subst i
          exact ok1395
        · by_cases h1396_1398 : i < 1397
          · have e : i = 1396 := by omega
            subst i
            exact ok1396
          · have e : i = 1397 := by omega
            subst i
            exact ok1397
    · by_cases h1398_1404 : i < 1401
      · by_cases h1398_1401 : i < 1399
        · have e : i = 1398 := by omega
          subst i
          exact ok1398
        · by_cases h1399_1401 : i < 1400
          · have e : i = 1399 := by omega
            subst i
            exact ok1399
          · have e : i = 1400 := by omega
            subst i
            exact ok1400
      · by_cases h1401_1404 : i < 1402
        · have e : i = 1401 := by omega
          subst i
          exact ok1401
        · by_cases h1402_1404 : i < 1403
          · have e : i = 1402 := by omega
            subst i
            exact ok1402
          · have e : i = 1403 := by omega
            subst i
            exact ok1403
  · by_cases h1404_1416 : i < 1410
    · by_cases h1404_1410 : i < 1407
      · by_cases h1404_1407 : i < 1405
        · have e : i = 1404 := by omega
          subst i
          exact ok1404
        · by_cases h1405_1407 : i < 1406
          · have e : i = 1405 := by omega
            subst i
            exact ok1405
          · have e : i = 1406 := by omega
            subst i
            exact ok1406
      · by_cases h1407_1410 : i < 1408
        · have e : i = 1407 := by omega
          subst i
          exact ok1407
        · by_cases h1408_1410 : i < 1409
          · have e : i = 1408 := by omega
            subst i
            exact ok1408
          · have e : i = 1409 := by omega
            subst i
            exact ok1409
    · by_cases h1410_1416 : i < 1413
      · by_cases h1410_1413 : i < 1411
        · have e : i = 1410 := by omega
          subst i
          exact ok1410
        · by_cases h1411_1413 : i < 1412
          · have e : i = 1411 := by omega
            subst i
            exact ok1411
          · have e : i = 1412 := by omega
            subst i
            exact ok1412
      · by_cases h1413_1416 : i < 1414
        · have e : i = 1413 := by omega
          subst i
          exact ok1413
        · by_cases h1414_1416 : i < 1415
          · have e : i = 1414 := by omega
            subst i
            exact ok1414
          · have e : i = 1415 := by omega
            subst i
            exact ok1415
end HaarHoneyData
