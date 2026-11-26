import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1536 : valid D 1536 := by decide +kernel
private theorem ok1537 : valid D 1537 := by decide +kernel
private theorem ok1538 : valid D 1538 := by decide +kernel
private theorem ok1539 : valid D 1539 := by decide +kernel
private theorem ok1540 : valid D 1540 := by decide +kernel
private theorem ok1541 : valid D 1541 := by decide +kernel
private theorem ok1542 : valid D 1542 := by decide +kernel
private theorem ok1543 : valid D 1543 := by decide +kernel
private theorem ok1544 : valid D 1544 := by decide +kernel
private theorem ok1545 : valid D 1545 := by decide +kernel
private theorem ok1546 : valid D 1546 := by decide +kernel
private theorem ok1547 : valid D 1547 := by decide +kernel
private theorem ok1548 : valid D 1548 := by decide +kernel
private theorem ok1549 : valid D 1549 := by decide +kernel
private theorem ok1550 : valid D 1550 := by decide +kernel
private theorem ok1551 : valid D 1551 := by decide +kernel
private theorem ok1552 : valid D 1552 := by decide +kernel
private theorem ok1553 : valid D 1553 := by decide +kernel
private theorem ok1554 : valid D 1554 := by decide +kernel
private theorem ok1555 : valid D 1555 := by decide +kernel
private theorem ok1556 : valid D 1556 := by decide +kernel
private theorem ok1557 : valid D 1557 := by decide +kernel
private theorem ok1558 : valid D 1558 := by decide +kernel
private theorem ok1559 : valid D 1559 := by decide +kernel
theorem C1536valid (i : Nat) (_lo : 1536 ≤ i) (_hi : i < 1560) : valid D i := by
  by_cases h1536_1560 : i < 1548
  · by_cases h1536_1548 : i < 1542
    · by_cases h1536_1542 : i < 1539
      · by_cases h1536_1539 : i < 1537
        · have e : i = 1536 := by omega
          subst i
          exact ok1536
        · by_cases h1537_1539 : i < 1538
          · have e : i = 1537 := by omega
            subst i
            exact ok1537
          · have e : i = 1538 := by omega
            subst i
            exact ok1538
      · by_cases h1539_1542 : i < 1540
        · have e : i = 1539 := by omega
          subst i
          exact ok1539
        · by_cases h1540_1542 : i < 1541
          · have e : i = 1540 := by omega
            subst i
            exact ok1540
          · have e : i = 1541 := by omega
            subst i
            exact ok1541
    · by_cases h1542_1548 : i < 1545
      · by_cases h1542_1545 : i < 1543
        · have e : i = 1542 := by omega
          subst i
          exact ok1542
        · by_cases h1543_1545 : i < 1544
          · have e : i = 1543 := by omega
            subst i
            exact ok1543
          · have e : i = 1544 := by omega
            subst i
            exact ok1544
      · by_cases h1545_1548 : i < 1546
        · have e : i = 1545 := by omega
          subst i
          exact ok1545
        · by_cases h1546_1548 : i < 1547
          · have e : i = 1546 := by omega
            subst i
            exact ok1546
          · have e : i = 1547 := by omega
            subst i
            exact ok1547
  · by_cases h1548_1560 : i < 1554
    · by_cases h1548_1554 : i < 1551
      · by_cases h1548_1551 : i < 1549
        · have e : i = 1548 := by omega
          subst i
          exact ok1548
        · by_cases h1549_1551 : i < 1550
          · have e : i = 1549 := by omega
            subst i
            exact ok1549
          · have e : i = 1550 := by omega
            subst i
            exact ok1550
      · by_cases h1551_1554 : i < 1552
        · have e : i = 1551 := by omega
          subst i
          exact ok1551
        · by_cases h1552_1554 : i < 1553
          · have e : i = 1552 := by omega
            subst i
            exact ok1552
          · have e : i = 1553 := by omega
            subst i
            exact ok1553
    · by_cases h1554_1560 : i < 1557
      · by_cases h1554_1557 : i < 1555
        · have e : i = 1554 := by omega
          subst i
          exact ok1554
        · by_cases h1555_1557 : i < 1556
          · have e : i = 1555 := by omega
            subst i
            exact ok1555
          · have e : i = 1556 := by omega
            subst i
            exact ok1556
      · by_cases h1557_1560 : i < 1558
        · have e : i = 1557 := by omega
          subst i
          exact ok1557
        · by_cases h1558_1560 : i < 1559
          · have e : i = 1558 := by omega
            subst i
            exact ok1558
          · have e : i = 1559 := by omega
            subst i
            exact ok1559
end HaarHoneyData
