import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1416 : valid D 1416 := by decide +kernel
private theorem ok1417 : valid D 1417 := by decide +kernel
private theorem ok1418 : valid D 1418 := by decide +kernel
private theorem ok1419 : valid D 1419 := by decide +kernel
private theorem ok1420 : valid D 1420 := by decide +kernel
private theorem ok1421 : valid D 1421 := by decide +kernel
private theorem ok1422 : valid D 1422 := by decide +kernel
private theorem ok1423 : valid D 1423 := by decide +kernel
private theorem ok1424 : valid D 1424 := by decide +kernel
private theorem ok1425 : valid D 1425 := by decide +kernel
private theorem ok1426 : valid D 1426 := by decide +kernel
private theorem ok1427 : valid D 1427 := by decide +kernel
private theorem ok1428 : valid D 1428 := by decide +kernel
private theorem ok1429 : valid D 1429 := by decide +kernel
private theorem ok1430 : valid D 1430 := by decide +kernel
private theorem ok1431 : valid D 1431 := by decide +kernel
private theorem ok1432 : valid D 1432 := by decide +kernel
private theorem ok1433 : valid D 1433 := by decide +kernel
private theorem ok1434 : valid D 1434 := by decide +kernel
private theorem ok1435 : valid D 1435 := by decide +kernel
private theorem ok1436 : valid D 1436 := by decide +kernel
private theorem ok1437 : valid D 1437 := by decide +kernel
private theorem ok1438 : valid D 1438 := by decide +kernel
private theorem ok1439 : valid D 1439 := by decide +kernel
theorem C1416valid (i : Nat) (_lo : 1416 ≤ i) (_hi : i < 1440) : valid D i := by
  by_cases h1416_1440 : i < 1428
  · by_cases h1416_1428 : i < 1422
    · by_cases h1416_1422 : i < 1419
      · by_cases h1416_1419 : i < 1417
        · have e : i = 1416 := by omega
          subst i
          exact ok1416
        · by_cases h1417_1419 : i < 1418
          · have e : i = 1417 := by omega
            subst i
            exact ok1417
          · have e : i = 1418 := by omega
            subst i
            exact ok1418
      · by_cases h1419_1422 : i < 1420
        · have e : i = 1419 := by omega
          subst i
          exact ok1419
        · by_cases h1420_1422 : i < 1421
          · have e : i = 1420 := by omega
            subst i
            exact ok1420
          · have e : i = 1421 := by omega
            subst i
            exact ok1421
    · by_cases h1422_1428 : i < 1425
      · by_cases h1422_1425 : i < 1423
        · have e : i = 1422 := by omega
          subst i
          exact ok1422
        · by_cases h1423_1425 : i < 1424
          · have e : i = 1423 := by omega
            subst i
            exact ok1423
          · have e : i = 1424 := by omega
            subst i
            exact ok1424
      · by_cases h1425_1428 : i < 1426
        · have e : i = 1425 := by omega
          subst i
          exact ok1425
        · by_cases h1426_1428 : i < 1427
          · have e : i = 1426 := by omega
            subst i
            exact ok1426
          · have e : i = 1427 := by omega
            subst i
            exact ok1427
  · by_cases h1428_1440 : i < 1434
    · by_cases h1428_1434 : i < 1431
      · by_cases h1428_1431 : i < 1429
        · have e : i = 1428 := by omega
          subst i
          exact ok1428
        · by_cases h1429_1431 : i < 1430
          · have e : i = 1429 := by omega
            subst i
            exact ok1429
          · have e : i = 1430 := by omega
            subst i
            exact ok1430
      · by_cases h1431_1434 : i < 1432
        · have e : i = 1431 := by omega
          subst i
          exact ok1431
        · by_cases h1432_1434 : i < 1433
          · have e : i = 1432 := by omega
            subst i
            exact ok1432
          · have e : i = 1433 := by omega
            subst i
            exact ok1433
    · by_cases h1434_1440 : i < 1437
      · by_cases h1434_1437 : i < 1435
        · have e : i = 1434 := by omega
          subst i
          exact ok1434
        · by_cases h1435_1437 : i < 1436
          · have e : i = 1435 := by omega
            subst i
            exact ok1435
          · have e : i = 1436 := by omega
            subst i
            exact ok1436
      · by_cases h1437_1440 : i < 1438
        · have e : i = 1437 := by omega
          subst i
          exact ok1437
        · by_cases h1438_1440 : i < 1439
          · have e : i = 1438 := by omega
            subst i
            exact ok1438
          · have e : i = 1439 := by omega
            subst i
            exact ok1439
end HaarHoneyData
