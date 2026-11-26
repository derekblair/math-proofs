import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1584 : valid D 1584 := by decide +kernel
private theorem ok1585 : valid D 1585 := by decide +kernel
private theorem ok1586 : valid D 1586 := by decide +kernel
private theorem ok1587 : valid D 1587 := by decide +kernel
private theorem ok1588 : valid D 1588 := by decide +kernel
private theorem ok1589 : valid D 1589 := by decide +kernel
private theorem ok1590 : valid D 1590 := by decide +kernel
private theorem ok1591 : valid D 1591 := by decide +kernel
private theorem ok1592 : valid D 1592 := by decide +kernel
private theorem ok1593 : valid D 1593 := by decide +kernel
private theorem ok1594 : valid D 1594 := by decide +kernel
private theorem ok1595 : valid D 1595 := by decide +kernel
private theorem ok1596 : valid D 1596 := by decide +kernel
private theorem ok1597 : valid D 1597 := by decide +kernel
private theorem ok1598 : valid D 1598 := by decide +kernel
private theorem ok1599 : valid D 1599 := by decide +kernel
private theorem ok1600 : valid D 1600 := by decide +kernel
private theorem ok1601 : valid D 1601 := by decide +kernel
private theorem ok1602 : valid D 1602 := by decide +kernel
private theorem ok1603 : valid D 1603 := by decide +kernel
private theorem ok1604 : valid D 1604 := by decide +kernel
private theorem ok1605 : valid D 1605 := by decide +kernel
private theorem ok1606 : valid D 1606 := by decide +kernel
private theorem ok1607 : valid D 1607 := by decide +kernel
theorem C1584valid (i : Nat) (_lo : 1584 ≤ i) (_hi : i < 1608) : valid D i := by
  by_cases h1584_1608 : i < 1596
  · by_cases h1584_1596 : i < 1590
    · by_cases h1584_1590 : i < 1587
      · by_cases h1584_1587 : i < 1585
        · have e : i = 1584 := by omega
          subst i
          exact ok1584
        · by_cases h1585_1587 : i < 1586
          · have e : i = 1585 := by omega
            subst i
            exact ok1585
          · have e : i = 1586 := by omega
            subst i
            exact ok1586
      · by_cases h1587_1590 : i < 1588
        · have e : i = 1587 := by omega
          subst i
          exact ok1587
        · by_cases h1588_1590 : i < 1589
          · have e : i = 1588 := by omega
            subst i
            exact ok1588
          · have e : i = 1589 := by omega
            subst i
            exact ok1589
    · by_cases h1590_1596 : i < 1593
      · by_cases h1590_1593 : i < 1591
        · have e : i = 1590 := by omega
          subst i
          exact ok1590
        · by_cases h1591_1593 : i < 1592
          · have e : i = 1591 := by omega
            subst i
            exact ok1591
          · have e : i = 1592 := by omega
            subst i
            exact ok1592
      · by_cases h1593_1596 : i < 1594
        · have e : i = 1593 := by omega
          subst i
          exact ok1593
        · by_cases h1594_1596 : i < 1595
          · have e : i = 1594 := by omega
            subst i
            exact ok1594
          · have e : i = 1595 := by omega
            subst i
            exact ok1595
  · by_cases h1596_1608 : i < 1602
    · by_cases h1596_1602 : i < 1599
      · by_cases h1596_1599 : i < 1597
        · have e : i = 1596 := by omega
          subst i
          exact ok1596
        · by_cases h1597_1599 : i < 1598
          · have e : i = 1597 := by omega
            subst i
            exact ok1597
          · have e : i = 1598 := by omega
            subst i
            exact ok1598
      · by_cases h1599_1602 : i < 1600
        · have e : i = 1599 := by omega
          subst i
          exact ok1599
        · by_cases h1600_1602 : i < 1601
          · have e : i = 1600 := by omega
            subst i
            exact ok1600
          · have e : i = 1601 := by omega
            subst i
            exact ok1601
    · by_cases h1602_1608 : i < 1605
      · by_cases h1602_1605 : i < 1603
        · have e : i = 1602 := by omega
          subst i
          exact ok1602
        · by_cases h1603_1605 : i < 1604
          · have e : i = 1603 := by omega
            subst i
            exact ok1603
          · have e : i = 1604 := by omega
            subst i
            exact ok1604
      · by_cases h1605_1608 : i < 1606
        · have e : i = 1605 := by omega
          subst i
          exact ok1605
        · by_cases h1606_1608 : i < 1607
          · have e : i = 1606 := by omega
            subst i
            exact ok1606
          · have e : i = 1607 := by omega
            subst i
            exact ok1607
end HaarHoneyData
