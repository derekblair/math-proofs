import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1608 : valid D 1608 := by decide +kernel
private theorem ok1609 : valid D 1609 := by decide +kernel
private theorem ok1610 : valid D 1610 := by decide +kernel
private theorem ok1611 : valid D 1611 := by decide +kernel
private theorem ok1612 : valid D 1612 := by decide +kernel
private theorem ok1613 : valid D 1613 := by decide +kernel
private theorem ok1614 : valid D 1614 := by decide +kernel
private theorem ok1615 : valid D 1615 := by decide +kernel
private theorem ok1616 : valid D 1616 := by decide +kernel
private theorem ok1617 : valid D 1617 := by decide +kernel
private theorem ok1618 : valid D 1618 := by decide +kernel
private theorem ok1619 : valid D 1619 := by decide +kernel
private theorem ok1620 : valid D 1620 := by decide +kernel
private theorem ok1621 : valid D 1621 := by decide +kernel
private theorem ok1622 : valid D 1622 := by decide +kernel
private theorem ok1623 : valid D 1623 := by decide +kernel
private theorem ok1624 : valid D 1624 := by decide +kernel
private theorem ok1625 : valid D 1625 := by decide +kernel
private theorem ok1626 : valid D 1626 := by decide +kernel
private theorem ok1627 : valid D 1627 := by decide +kernel
private theorem ok1628 : valid D 1628 := by decide +kernel
private theorem ok1629 : valid D 1629 := by decide +kernel
private theorem ok1630 : valid D 1630 := by decide +kernel
private theorem ok1631 : valid D 1631 := by decide +kernel
theorem C1608valid (i : Nat) (_lo : 1608 ≤ i) (_hi : i < 1632) : valid D i := by
  by_cases h1608_1632 : i < 1620
  · by_cases h1608_1620 : i < 1614
    · by_cases h1608_1614 : i < 1611
      · by_cases h1608_1611 : i < 1609
        · have e : i = 1608 := by omega
          subst i
          exact ok1608
        · by_cases h1609_1611 : i < 1610
          · have e : i = 1609 := by omega
            subst i
            exact ok1609
          · have e : i = 1610 := by omega
            subst i
            exact ok1610
      · by_cases h1611_1614 : i < 1612
        · have e : i = 1611 := by omega
          subst i
          exact ok1611
        · by_cases h1612_1614 : i < 1613
          · have e : i = 1612 := by omega
            subst i
            exact ok1612
          · have e : i = 1613 := by omega
            subst i
            exact ok1613
    · by_cases h1614_1620 : i < 1617
      · by_cases h1614_1617 : i < 1615
        · have e : i = 1614 := by omega
          subst i
          exact ok1614
        · by_cases h1615_1617 : i < 1616
          · have e : i = 1615 := by omega
            subst i
            exact ok1615
          · have e : i = 1616 := by omega
            subst i
            exact ok1616
      · by_cases h1617_1620 : i < 1618
        · have e : i = 1617 := by omega
          subst i
          exact ok1617
        · by_cases h1618_1620 : i < 1619
          · have e : i = 1618 := by omega
            subst i
            exact ok1618
          · have e : i = 1619 := by omega
            subst i
            exact ok1619
  · by_cases h1620_1632 : i < 1626
    · by_cases h1620_1626 : i < 1623
      · by_cases h1620_1623 : i < 1621
        · have e : i = 1620 := by omega
          subst i
          exact ok1620
        · by_cases h1621_1623 : i < 1622
          · have e : i = 1621 := by omega
            subst i
            exact ok1621
          · have e : i = 1622 := by omega
            subst i
            exact ok1622
      · by_cases h1623_1626 : i < 1624
        · have e : i = 1623 := by omega
          subst i
          exact ok1623
        · by_cases h1624_1626 : i < 1625
          · have e : i = 1624 := by omega
            subst i
            exact ok1624
          · have e : i = 1625 := by omega
            subst i
            exact ok1625
    · by_cases h1626_1632 : i < 1629
      · by_cases h1626_1629 : i < 1627
        · have e : i = 1626 := by omega
          subst i
          exact ok1626
        · by_cases h1627_1629 : i < 1628
          · have e : i = 1627 := by omega
            subst i
            exact ok1627
          · have e : i = 1628 := by omega
            subst i
            exact ok1628
      · by_cases h1629_1632 : i < 1630
        · have e : i = 1629 := by omega
          subst i
          exact ok1629
        · by_cases h1630_1632 : i < 1631
          · have e : i = 1630 := by omega
            subst i
            exact ok1630
          · have e : i = 1631 := by omega
            subst i
            exact ok1631
end HaarHoneyData
