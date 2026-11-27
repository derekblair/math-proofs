import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1560 : valid D 1560 := by decide +kernel
private theorem ok1561 : valid D 1561 := by decide +kernel
private theorem ok1562 : valid D 1562 := by decide +kernel
private theorem ok1563 : valid D 1563 := by decide +kernel
private theorem ok1564 : valid D 1564 := by decide +kernel
private theorem ok1565 : valid D 1565 := by decide +kernel
private theorem ok1566 : valid D 1566 := by decide +kernel
private theorem ok1567 : valid D 1567 := by decide +kernel
private theorem ok1568 : valid D 1568 := by decide +kernel
private theorem ok1569 : valid D 1569 := by decide +kernel
private theorem ok1570 : valid D 1570 := by decide +kernel
private theorem ok1571 : valid D 1571 := by decide +kernel
private theorem ok1572 : valid D 1572 := by decide +kernel
private theorem ok1573 : valid D 1573 := by decide +kernel
private theorem ok1574 : valid D 1574 := by decide +kernel
private theorem ok1575 : valid D 1575 := by decide +kernel
private theorem ok1576 : valid D 1576 := by decide +kernel
private theorem ok1577 : valid D 1577 := by decide +kernel
private theorem ok1578 : valid D 1578 := by decide +kernel
private theorem ok1579 : valid D 1579 := by decide +kernel
private theorem ok1580 : valid D 1580 := by decide +kernel
private theorem ok1581 : valid D 1581 := by decide +kernel
private theorem ok1582 : valid D 1582 := by decide +kernel
private theorem ok1583 : valid D 1583 := by decide +kernel
theorem C1560valid (i : Nat) (_lo : 1560 ≤ i) (_hi : i < 1584) : valid D i := by
  by_cases h1560_1584 : i < 1572
  · by_cases h1560_1572 : i < 1566
    · by_cases h1560_1566 : i < 1563
      · by_cases h1560_1563 : i < 1561
        · have e : i = 1560 := by omega
          subst i
          exact ok1560
        · by_cases h1561_1563 : i < 1562
          · have e : i = 1561 := by omega
            subst i
            exact ok1561
          · have e : i = 1562 := by omega
            subst i
            exact ok1562
      · by_cases h1563_1566 : i < 1564
        · have e : i = 1563 := by omega
          subst i
          exact ok1563
        · by_cases h1564_1566 : i < 1565
          · have e : i = 1564 := by omega
            subst i
            exact ok1564
          · have e : i = 1565 := by omega
            subst i
            exact ok1565
    · by_cases h1566_1572 : i < 1569
      · by_cases h1566_1569 : i < 1567
        · have e : i = 1566 := by omega
          subst i
          exact ok1566
        · by_cases h1567_1569 : i < 1568
          · have e : i = 1567 := by omega
            subst i
            exact ok1567
          · have e : i = 1568 := by omega
            subst i
            exact ok1568
      · by_cases h1569_1572 : i < 1570
        · have e : i = 1569 := by omega
          subst i
          exact ok1569
        · by_cases h1570_1572 : i < 1571
          · have e : i = 1570 := by omega
            subst i
            exact ok1570
          · have e : i = 1571 := by omega
            subst i
            exact ok1571
  · by_cases h1572_1584 : i < 1578
    · by_cases h1572_1578 : i < 1575
      · by_cases h1572_1575 : i < 1573
        · have e : i = 1572 := by omega
          subst i
          exact ok1572
        · by_cases h1573_1575 : i < 1574
          · have e : i = 1573 := by omega
            subst i
            exact ok1573
          · have e : i = 1574 := by omega
            subst i
            exact ok1574
      · by_cases h1575_1578 : i < 1576
        · have e : i = 1575 := by omega
          subst i
          exact ok1575
        · by_cases h1576_1578 : i < 1577
          · have e : i = 1576 := by omega
            subst i
            exact ok1576
          · have e : i = 1577 := by omega
            subst i
            exact ok1577
    · by_cases h1578_1584 : i < 1581
      · by_cases h1578_1581 : i < 1579
        · have e : i = 1578 := by omega
          subst i
          exact ok1578
        · by_cases h1579_1581 : i < 1580
          · have e : i = 1579 := by omega
            subst i
            exact ok1579
          · have e : i = 1580 := by omega
            subst i
            exact ok1580
      · by_cases h1581_1584 : i < 1582
        · have e : i = 1581 := by omega
          subst i
          exact ok1581
        · by_cases h1582_1584 : i < 1583
          · have e : i = 1582 := by omega
            subst i
            exact ok1582
          · have e : i = 1583 := by omega
            subst i
            exact ok1583
end HaarHoneyData
