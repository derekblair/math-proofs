import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1632 : valid D 1632 := by decide +kernel
private theorem ok1633 : valid D 1633 := by decide +kernel
private theorem ok1634 : valid D 1634 := by decide +kernel
private theorem ok1635 : valid D 1635 := by decide +kernel
private theorem ok1636 : valid D 1636 := by decide +kernel
private theorem ok1637 : valid D 1637 := by decide +kernel
private theorem ok1638 : valid D 1638 := by decide +kernel
private theorem ok1639 : valid D 1639 := by decide +kernel
private theorem ok1640 : valid D 1640 := by decide +kernel
private theorem ok1641 : valid D 1641 := by decide +kernel
private theorem ok1642 : valid D 1642 := by decide +kernel
private theorem ok1643 : valid D 1643 := by decide +kernel
private theorem ok1644 : valid D 1644 := by decide +kernel
private theorem ok1645 : valid D 1645 := by decide +kernel
private theorem ok1646 : valid D 1646 := by decide +kernel
private theorem ok1647 : valid D 1647 := by decide +kernel
private theorem ok1648 : valid D 1648 := by decide +kernel
private theorem ok1649 : valid D 1649 := by decide +kernel
private theorem ok1650 : valid D 1650 := by decide +kernel
private theorem ok1651 : valid D 1651 := by decide +kernel
private theorem ok1652 : valid D 1652 := by decide +kernel
private theorem ok1653 : valid D 1653 := by decide +kernel
private theorem ok1654 : valid D 1654 := by decide +kernel
private theorem ok1655 : valid D 1655 := by decide +kernel
theorem C1632valid (i : Nat) (_lo : 1632 ≤ i) (_hi : i < 1656) : valid D i := by
  by_cases h1632_1656 : i < 1644
  · by_cases h1632_1644 : i < 1638
    · by_cases h1632_1638 : i < 1635
      · by_cases h1632_1635 : i < 1633
        · have e : i = 1632 := by omega
          subst i
          exact ok1632
        · by_cases h1633_1635 : i < 1634
          · have e : i = 1633 := by omega
            subst i
            exact ok1633
          · have e : i = 1634 := by omega
            subst i
            exact ok1634
      · by_cases h1635_1638 : i < 1636
        · have e : i = 1635 := by omega
          subst i
          exact ok1635
        · by_cases h1636_1638 : i < 1637
          · have e : i = 1636 := by omega
            subst i
            exact ok1636
          · have e : i = 1637 := by omega
            subst i
            exact ok1637
    · by_cases h1638_1644 : i < 1641
      · by_cases h1638_1641 : i < 1639
        · have e : i = 1638 := by omega
          subst i
          exact ok1638
        · by_cases h1639_1641 : i < 1640
          · have e : i = 1639 := by omega
            subst i
            exact ok1639
          · have e : i = 1640 := by omega
            subst i
            exact ok1640
      · by_cases h1641_1644 : i < 1642
        · have e : i = 1641 := by omega
          subst i
          exact ok1641
        · by_cases h1642_1644 : i < 1643
          · have e : i = 1642 := by omega
            subst i
            exact ok1642
          · have e : i = 1643 := by omega
            subst i
            exact ok1643
  · by_cases h1644_1656 : i < 1650
    · by_cases h1644_1650 : i < 1647
      · by_cases h1644_1647 : i < 1645
        · have e : i = 1644 := by omega
          subst i
          exact ok1644
        · by_cases h1645_1647 : i < 1646
          · have e : i = 1645 := by omega
            subst i
            exact ok1645
          · have e : i = 1646 := by omega
            subst i
            exact ok1646
      · by_cases h1647_1650 : i < 1648
        · have e : i = 1647 := by omega
          subst i
          exact ok1647
        · by_cases h1648_1650 : i < 1649
          · have e : i = 1648 := by omega
            subst i
            exact ok1648
          · have e : i = 1649 := by omega
            subst i
            exact ok1649
    · by_cases h1650_1656 : i < 1653
      · by_cases h1650_1653 : i < 1651
        · have e : i = 1650 := by omega
          subst i
          exact ok1650
        · by_cases h1651_1653 : i < 1652
          · have e : i = 1651 := by omega
            subst i
            exact ok1651
          · have e : i = 1652 := by omega
            subst i
            exact ok1652
      · by_cases h1653_1656 : i < 1654
        · have e : i = 1653 := by omega
          subst i
          exact ok1653
        · by_cases h1654_1656 : i < 1655
          · have e : i = 1654 := by omega
            subst i
            exact ok1654
          · have e : i = 1655 := by omega
            subst i
            exact ok1655
end HaarHoneyData
