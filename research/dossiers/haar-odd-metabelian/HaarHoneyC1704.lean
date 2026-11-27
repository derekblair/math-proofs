import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1704 : valid D 1704 := by decide +kernel
private theorem ok1705 : valid D 1705 := by decide +kernel
private theorem ok1706 : valid D 1706 := by decide +kernel
private theorem ok1707 : valid D 1707 := by decide +kernel
private theorem ok1708 : valid D 1708 := by decide +kernel
private theorem ok1709 : valid D 1709 := by decide +kernel
private theorem ok1710 : valid D 1710 := by decide +kernel
private theorem ok1711 : valid D 1711 := by decide +kernel
private theorem ok1712 : valid D 1712 := by decide +kernel
private theorem ok1713 : valid D 1713 := by decide +kernel
private theorem ok1714 : valid D 1714 := by decide +kernel
private theorem ok1715 : valid D 1715 := by decide +kernel
private theorem ok1716 : valid D 1716 := by decide +kernel
private theorem ok1717 : valid D 1717 := by decide +kernel
private theorem ok1718 : valid D 1718 := by decide +kernel
private theorem ok1719 : valid D 1719 := by decide +kernel
private theorem ok1720 : valid D 1720 := by decide +kernel
private theorem ok1721 : valid D 1721 := by decide +kernel
private theorem ok1722 : valid D 1722 := by decide +kernel
private theorem ok1723 : valid D 1723 := by decide +kernel
private theorem ok1724 : valid D 1724 := by decide +kernel
private theorem ok1725 : valid D 1725 := by decide +kernel
private theorem ok1726 : valid D 1726 := by decide +kernel
private theorem ok1727 : valid D 1727 := by decide +kernel
theorem C1704valid (i : Nat) (_lo : 1704 ≤ i) (_hi : i < 1728) : valid D i := by
  by_cases h1704_1728 : i < 1716
  · by_cases h1704_1716 : i < 1710
    · by_cases h1704_1710 : i < 1707
      · by_cases h1704_1707 : i < 1705
        · have e : i = 1704 := by omega
          subst i
          exact ok1704
        · by_cases h1705_1707 : i < 1706
          · have e : i = 1705 := by omega
            subst i
            exact ok1705
          · have e : i = 1706 := by omega
            subst i
            exact ok1706
      · by_cases h1707_1710 : i < 1708
        · have e : i = 1707 := by omega
          subst i
          exact ok1707
        · by_cases h1708_1710 : i < 1709
          · have e : i = 1708 := by omega
            subst i
            exact ok1708
          · have e : i = 1709 := by omega
            subst i
            exact ok1709
    · by_cases h1710_1716 : i < 1713
      · by_cases h1710_1713 : i < 1711
        · have e : i = 1710 := by omega
          subst i
          exact ok1710
        · by_cases h1711_1713 : i < 1712
          · have e : i = 1711 := by omega
            subst i
            exact ok1711
          · have e : i = 1712 := by omega
            subst i
            exact ok1712
      · by_cases h1713_1716 : i < 1714
        · have e : i = 1713 := by omega
          subst i
          exact ok1713
        · by_cases h1714_1716 : i < 1715
          · have e : i = 1714 := by omega
            subst i
            exact ok1714
          · have e : i = 1715 := by omega
            subst i
            exact ok1715
  · by_cases h1716_1728 : i < 1722
    · by_cases h1716_1722 : i < 1719
      · by_cases h1716_1719 : i < 1717
        · have e : i = 1716 := by omega
          subst i
          exact ok1716
        · by_cases h1717_1719 : i < 1718
          · have e : i = 1717 := by omega
            subst i
            exact ok1717
          · have e : i = 1718 := by omega
            subst i
            exact ok1718
      · by_cases h1719_1722 : i < 1720
        · have e : i = 1719 := by omega
          subst i
          exact ok1719
        · by_cases h1720_1722 : i < 1721
          · have e : i = 1720 := by omega
            subst i
            exact ok1720
          · have e : i = 1721 := by omega
            subst i
            exact ok1721
    · by_cases h1722_1728 : i < 1725
      · by_cases h1722_1725 : i < 1723
        · have e : i = 1722 := by omega
          subst i
          exact ok1722
        · by_cases h1723_1725 : i < 1724
          · have e : i = 1723 := by omega
            subst i
            exact ok1723
          · have e : i = 1724 := by omega
            subst i
            exact ok1724
      · by_cases h1725_1728 : i < 1726
        · have e : i = 1725 := by omega
          subst i
          exact ok1725
        · by_cases h1726_1728 : i < 1727
          · have e : i = 1726 := by omega
            subst i
            exact ok1726
          · have e : i = 1727 := by omega
            subst i
            exact ok1727
end HaarHoneyData
