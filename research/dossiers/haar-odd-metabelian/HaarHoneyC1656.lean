import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1656 : valid D 1656 := by decide +kernel
private theorem ok1657 : valid D 1657 := by decide +kernel
private theorem ok1658 : valid D 1658 := by decide +kernel
private theorem ok1659 : valid D 1659 := by decide +kernel
private theorem ok1660 : valid D 1660 := by decide +kernel
private theorem ok1661 : valid D 1661 := by decide +kernel
private theorem ok1662 : valid D 1662 := by decide +kernel
private theorem ok1663 : valid D 1663 := by decide +kernel
private theorem ok1664 : valid D 1664 := by decide +kernel
private theorem ok1665 : valid D 1665 := by decide +kernel
private theorem ok1666 : valid D 1666 := by decide +kernel
private theorem ok1667 : valid D 1667 := by decide +kernel
private theorem ok1668 : valid D 1668 := by decide +kernel
private theorem ok1669 : valid D 1669 := by decide +kernel
private theorem ok1670 : valid D 1670 := by decide +kernel
private theorem ok1671 : valid D 1671 := by decide +kernel
private theorem ok1672 : valid D 1672 := by decide +kernel
private theorem ok1673 : valid D 1673 := by decide +kernel
private theorem ok1674 : valid D 1674 := by decide +kernel
private theorem ok1675 : valid D 1675 := by decide +kernel
private theorem ok1676 : valid D 1676 := by decide +kernel
private theorem ok1677 : valid D 1677 := by decide +kernel
private theorem ok1678 : valid D 1678 := by decide +kernel
private theorem ok1679 : valid D 1679 := by decide +kernel
theorem C1656valid (i : Nat) (_lo : 1656 ≤ i) (_hi : i < 1680) : valid D i := by
  by_cases h1656_1680 : i < 1668
  · by_cases h1656_1668 : i < 1662
    · by_cases h1656_1662 : i < 1659
      · by_cases h1656_1659 : i < 1657
        · have e : i = 1656 := by omega
          subst i
          exact ok1656
        · by_cases h1657_1659 : i < 1658
          · have e : i = 1657 := by omega
            subst i
            exact ok1657
          · have e : i = 1658 := by omega
            subst i
            exact ok1658
      · by_cases h1659_1662 : i < 1660
        · have e : i = 1659 := by omega
          subst i
          exact ok1659
        · by_cases h1660_1662 : i < 1661
          · have e : i = 1660 := by omega
            subst i
            exact ok1660
          · have e : i = 1661 := by omega
            subst i
            exact ok1661
    · by_cases h1662_1668 : i < 1665
      · by_cases h1662_1665 : i < 1663
        · have e : i = 1662 := by omega
          subst i
          exact ok1662
        · by_cases h1663_1665 : i < 1664
          · have e : i = 1663 := by omega
            subst i
            exact ok1663
          · have e : i = 1664 := by omega
            subst i
            exact ok1664
      · by_cases h1665_1668 : i < 1666
        · have e : i = 1665 := by omega
          subst i
          exact ok1665
        · by_cases h1666_1668 : i < 1667
          · have e : i = 1666 := by omega
            subst i
            exact ok1666
          · have e : i = 1667 := by omega
            subst i
            exact ok1667
  · by_cases h1668_1680 : i < 1674
    · by_cases h1668_1674 : i < 1671
      · by_cases h1668_1671 : i < 1669
        · have e : i = 1668 := by omega
          subst i
          exact ok1668
        · by_cases h1669_1671 : i < 1670
          · have e : i = 1669 := by omega
            subst i
            exact ok1669
          · have e : i = 1670 := by omega
            subst i
            exact ok1670
      · by_cases h1671_1674 : i < 1672
        · have e : i = 1671 := by omega
          subst i
          exact ok1671
        · by_cases h1672_1674 : i < 1673
          · have e : i = 1672 := by omega
            subst i
            exact ok1672
          · have e : i = 1673 := by omega
            subst i
            exact ok1673
    · by_cases h1674_1680 : i < 1677
      · by_cases h1674_1677 : i < 1675
        · have e : i = 1674 := by omega
          subst i
          exact ok1674
        · by_cases h1675_1677 : i < 1676
          · have e : i = 1675 := by omega
            subst i
            exact ok1675
          · have e : i = 1676 := by omega
            subst i
            exact ok1676
      · by_cases h1677_1680 : i < 1678
        · have e : i = 1677 := by omega
          subst i
          exact ok1677
        · by_cases h1678_1680 : i < 1679
          · have e : i = 1678 := by omega
            subst i
            exact ok1678
          · have e : i = 1679 := by omega
            subst i
            exact ok1679
end HaarHoneyData
