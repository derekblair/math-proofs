import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1464 : valid D 1464 := by decide +kernel
private theorem ok1465 : valid D 1465 := by decide +kernel
private theorem ok1466 : valid D 1466 := by decide +kernel
private theorem ok1467 : valid D 1467 := by decide +kernel
private theorem ok1468 : valid D 1468 := by decide +kernel
private theorem ok1469 : valid D 1469 := by decide +kernel
private theorem ok1470 : valid D 1470 := by decide +kernel
private theorem ok1471 : valid D 1471 := by decide +kernel
private theorem ok1472 : valid D 1472 := by decide +kernel
private theorem ok1473 : valid D 1473 := by decide +kernel
private theorem ok1474 : valid D 1474 := by decide +kernel
private theorem ok1475 : valid D 1475 := by decide +kernel
private theorem ok1476 : valid D 1476 := by decide +kernel
private theorem ok1477 : valid D 1477 := by decide +kernel
private theorem ok1478 : valid D 1478 := by decide +kernel
private theorem ok1479 : valid D 1479 := by decide +kernel
private theorem ok1480 : valid D 1480 := by decide +kernel
private theorem ok1481 : valid D 1481 := by decide +kernel
private theorem ok1482 : valid D 1482 := by decide +kernel
private theorem ok1483 : valid D 1483 := by decide +kernel
private theorem ok1484 : valid D 1484 := by decide +kernel
private theorem ok1485 : valid D 1485 := by decide +kernel
private theorem ok1486 : valid D 1486 := by decide +kernel
private theorem ok1487 : valid D 1487 := by decide +kernel
theorem C1464valid (i : Nat) (_lo : 1464 ≤ i) (_hi : i < 1488) : valid D i := by
  by_cases h1464_1488 : i < 1476
  · by_cases h1464_1476 : i < 1470
    · by_cases h1464_1470 : i < 1467
      · by_cases h1464_1467 : i < 1465
        · have e : i = 1464 := by omega
          subst i
          exact ok1464
        · by_cases h1465_1467 : i < 1466
          · have e : i = 1465 := by omega
            subst i
            exact ok1465
          · have e : i = 1466 := by omega
            subst i
            exact ok1466
      · by_cases h1467_1470 : i < 1468
        · have e : i = 1467 := by omega
          subst i
          exact ok1467
        · by_cases h1468_1470 : i < 1469
          · have e : i = 1468 := by omega
            subst i
            exact ok1468
          · have e : i = 1469 := by omega
            subst i
            exact ok1469
    · by_cases h1470_1476 : i < 1473
      · by_cases h1470_1473 : i < 1471
        · have e : i = 1470 := by omega
          subst i
          exact ok1470
        · by_cases h1471_1473 : i < 1472
          · have e : i = 1471 := by omega
            subst i
            exact ok1471
          · have e : i = 1472 := by omega
            subst i
            exact ok1472
      · by_cases h1473_1476 : i < 1474
        · have e : i = 1473 := by omega
          subst i
          exact ok1473
        · by_cases h1474_1476 : i < 1475
          · have e : i = 1474 := by omega
            subst i
            exact ok1474
          · have e : i = 1475 := by omega
            subst i
            exact ok1475
  · by_cases h1476_1488 : i < 1482
    · by_cases h1476_1482 : i < 1479
      · by_cases h1476_1479 : i < 1477
        · have e : i = 1476 := by omega
          subst i
          exact ok1476
        · by_cases h1477_1479 : i < 1478
          · have e : i = 1477 := by omega
            subst i
            exact ok1477
          · have e : i = 1478 := by omega
            subst i
            exact ok1478
      · by_cases h1479_1482 : i < 1480
        · have e : i = 1479 := by omega
          subst i
          exact ok1479
        · by_cases h1480_1482 : i < 1481
          · have e : i = 1480 := by omega
            subst i
            exact ok1480
          · have e : i = 1481 := by omega
            subst i
            exact ok1481
    · by_cases h1482_1488 : i < 1485
      · by_cases h1482_1485 : i < 1483
        · have e : i = 1482 := by omega
          subst i
          exact ok1482
        · by_cases h1483_1485 : i < 1484
          · have e : i = 1483 := by omega
            subst i
            exact ok1483
          · have e : i = 1484 := by omega
            subst i
            exact ok1484
      · by_cases h1485_1488 : i < 1486
        · have e : i = 1485 := by omega
          subst i
          exact ok1485
        · by_cases h1486_1488 : i < 1487
          · have e : i = 1486 := by omega
            subst i
            exact ok1486
          · have e : i = 1487 := by omega
            subst i
            exact ok1487
end HaarHoneyData
