import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1512 : valid D 1512 := by decide +kernel
private theorem ok1513 : valid D 1513 := by decide +kernel
private theorem ok1514 : valid D 1514 := by decide +kernel
private theorem ok1515 : valid D 1515 := by decide +kernel
private theorem ok1516 : valid D 1516 := by decide +kernel
private theorem ok1517 : valid D 1517 := by decide +kernel
private theorem ok1518 : valid D 1518 := by decide +kernel
private theorem ok1519 : valid D 1519 := by decide +kernel
private theorem ok1520 : valid D 1520 := by decide +kernel
private theorem ok1521 : valid D 1521 := by decide +kernel
private theorem ok1522 : valid D 1522 := by decide +kernel
private theorem ok1523 : valid D 1523 := by decide +kernel
private theorem ok1524 : valid D 1524 := by decide +kernel
private theorem ok1525 : valid D 1525 := by decide +kernel
private theorem ok1526 : valid D 1526 := by decide +kernel
private theorem ok1527 : valid D 1527 := by decide +kernel
private theorem ok1528 : valid D 1528 := by decide +kernel
private theorem ok1529 : valid D 1529 := by decide +kernel
private theorem ok1530 : valid D 1530 := by decide +kernel
private theorem ok1531 : valid D 1531 := by decide +kernel
private theorem ok1532 : valid D 1532 := by decide +kernel
private theorem ok1533 : valid D 1533 := by decide +kernel
private theorem ok1534 : valid D 1534 := by decide +kernel
private theorem ok1535 : valid D 1535 := by decide +kernel
theorem C1512valid (i : Nat) (_lo : 1512 ≤ i) (_hi : i < 1536) : valid D i := by
  by_cases h1512_1536 : i < 1524
  · by_cases h1512_1524 : i < 1518
    · by_cases h1512_1518 : i < 1515
      · by_cases h1512_1515 : i < 1513
        · have e : i = 1512 := by omega
          subst i
          exact ok1512
        · by_cases h1513_1515 : i < 1514
          · have e : i = 1513 := by omega
            subst i
            exact ok1513
          · have e : i = 1514 := by omega
            subst i
            exact ok1514
      · by_cases h1515_1518 : i < 1516
        · have e : i = 1515 := by omega
          subst i
          exact ok1515
        · by_cases h1516_1518 : i < 1517
          · have e : i = 1516 := by omega
            subst i
            exact ok1516
          · have e : i = 1517 := by omega
            subst i
            exact ok1517
    · by_cases h1518_1524 : i < 1521
      · by_cases h1518_1521 : i < 1519
        · have e : i = 1518 := by omega
          subst i
          exact ok1518
        · by_cases h1519_1521 : i < 1520
          · have e : i = 1519 := by omega
            subst i
            exact ok1519
          · have e : i = 1520 := by omega
            subst i
            exact ok1520
      · by_cases h1521_1524 : i < 1522
        · have e : i = 1521 := by omega
          subst i
          exact ok1521
        · by_cases h1522_1524 : i < 1523
          · have e : i = 1522 := by omega
            subst i
            exact ok1522
          · have e : i = 1523 := by omega
            subst i
            exact ok1523
  · by_cases h1524_1536 : i < 1530
    · by_cases h1524_1530 : i < 1527
      · by_cases h1524_1527 : i < 1525
        · have e : i = 1524 := by omega
          subst i
          exact ok1524
        · by_cases h1525_1527 : i < 1526
          · have e : i = 1525 := by omega
            subst i
            exact ok1525
          · have e : i = 1526 := by omega
            subst i
            exact ok1526
      · by_cases h1527_1530 : i < 1528
        · have e : i = 1527 := by omega
          subst i
          exact ok1527
        · by_cases h1528_1530 : i < 1529
          · have e : i = 1528 := by omega
            subst i
            exact ok1528
          · have e : i = 1529 := by omega
            subst i
            exact ok1529
    · by_cases h1530_1536 : i < 1533
      · by_cases h1530_1533 : i < 1531
        · have e : i = 1530 := by omega
          subst i
          exact ok1530
        · by_cases h1531_1533 : i < 1532
          · have e : i = 1531 := by omega
            subst i
            exact ok1531
          · have e : i = 1532 := by omega
            subst i
            exact ok1532
      · by_cases h1533_1536 : i < 1534
        · have e : i = 1533 := by omega
          subst i
          exact ok1533
        · by_cases h1534_1536 : i < 1535
          · have e : i = 1534 := by omega
            subst i
            exact ok1534
          · have e : i = 1535 := by omega
            subst i
            exact ok1535
end HaarHoneyData
