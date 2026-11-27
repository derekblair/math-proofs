import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1488 : valid D 1488 := by decide +kernel
private theorem ok1489 : valid D 1489 := by decide +kernel
private theorem ok1490 : valid D 1490 := by decide +kernel
private theorem ok1491 : valid D 1491 := by decide +kernel
private theorem ok1492 : valid D 1492 := by decide +kernel
private theorem ok1493 : valid D 1493 := by decide +kernel
private theorem ok1494 : valid D 1494 := by decide +kernel
private theorem ok1495 : valid D 1495 := by decide +kernel
private theorem ok1496 : valid D 1496 := by decide +kernel
private theorem ok1497 : valid D 1497 := by decide +kernel
private theorem ok1498 : valid D 1498 := by decide +kernel
private theorem ok1499 : valid D 1499 := by decide +kernel
private theorem ok1500 : valid D 1500 := by decide +kernel
private theorem ok1501 : valid D 1501 := by decide +kernel
private theorem ok1502 : valid D 1502 := by decide +kernel
private theorem ok1503 : valid D 1503 := by decide +kernel
private theorem ok1504 : valid D 1504 := by decide +kernel
private theorem ok1505 : valid D 1505 := by decide +kernel
private theorem ok1506 : valid D 1506 := by decide +kernel
private theorem ok1507 : valid D 1507 := by decide +kernel
private theorem ok1508 : valid D 1508 := by decide +kernel
private theorem ok1509 : valid D 1509 := by decide +kernel
private theorem ok1510 : valid D 1510 := by decide +kernel
private theorem ok1511 : valid D 1511 := by decide +kernel
theorem C1488valid (i : Nat) (_lo : 1488 ≤ i) (_hi : i < 1512) : valid D i := by
  by_cases h1488_1512 : i < 1500
  · by_cases h1488_1500 : i < 1494
    · by_cases h1488_1494 : i < 1491
      · by_cases h1488_1491 : i < 1489
        · have e : i = 1488 := by omega
          subst i
          exact ok1488
        · by_cases h1489_1491 : i < 1490
          · have e : i = 1489 := by omega
            subst i
            exact ok1489
          · have e : i = 1490 := by omega
            subst i
            exact ok1490
      · by_cases h1491_1494 : i < 1492
        · have e : i = 1491 := by omega
          subst i
          exact ok1491
        · by_cases h1492_1494 : i < 1493
          · have e : i = 1492 := by omega
            subst i
            exact ok1492
          · have e : i = 1493 := by omega
            subst i
            exact ok1493
    · by_cases h1494_1500 : i < 1497
      · by_cases h1494_1497 : i < 1495
        · have e : i = 1494 := by omega
          subst i
          exact ok1494
        · by_cases h1495_1497 : i < 1496
          · have e : i = 1495 := by omega
            subst i
            exact ok1495
          · have e : i = 1496 := by omega
            subst i
            exact ok1496
      · by_cases h1497_1500 : i < 1498
        · have e : i = 1497 := by omega
          subst i
          exact ok1497
        · by_cases h1498_1500 : i < 1499
          · have e : i = 1498 := by omega
            subst i
            exact ok1498
          · have e : i = 1499 := by omega
            subst i
            exact ok1499
  · by_cases h1500_1512 : i < 1506
    · by_cases h1500_1506 : i < 1503
      · by_cases h1500_1503 : i < 1501
        · have e : i = 1500 := by omega
          subst i
          exact ok1500
        · by_cases h1501_1503 : i < 1502
          · have e : i = 1501 := by omega
            subst i
            exact ok1501
          · have e : i = 1502 := by omega
            subst i
            exact ok1502
      · by_cases h1503_1506 : i < 1504
        · have e : i = 1503 := by omega
          subst i
          exact ok1503
        · by_cases h1504_1506 : i < 1505
          · have e : i = 1504 := by omega
            subst i
            exact ok1504
          · have e : i = 1505 := by omega
            subst i
            exact ok1505
    · by_cases h1506_1512 : i < 1509
      · by_cases h1506_1509 : i < 1507
        · have e : i = 1506 := by omega
          subst i
          exact ok1506
        · by_cases h1507_1509 : i < 1508
          · have e : i = 1507 := by omega
            subst i
            exact ok1507
          · have e : i = 1508 := by omega
            subst i
            exact ok1508
      · by_cases h1509_1512 : i < 1510
        · have e : i = 1509 := by omega
          subst i
          exact ok1509
        · by_cases h1510_1512 : i < 1511
          · have e : i = 1510 := by omega
            subst i
            exact ok1510
          · have e : i = 1511 := by omega
            subst i
            exact ok1511
end HaarHoneyData
