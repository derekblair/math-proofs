import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1728 : valid D 1728 := by decide +kernel
private theorem ok1729 : valid D 1729 := by decide +kernel
private theorem ok1730 : valid D 1730 := by decide +kernel
private theorem ok1731 : valid D 1731 := by decide +kernel
private theorem ok1732 : valid D 1732 := by decide +kernel
private theorem ok1733 : valid D 1733 := by decide +kernel
private theorem ok1734 : valid D 1734 := by decide +kernel
private theorem ok1735 : valid D 1735 := by decide +kernel
private theorem ok1736 : valid D 1736 := by decide +kernel
private theorem ok1737 : valid D 1737 := by decide +kernel
private theorem ok1738 : valid D 1738 := by decide +kernel
private theorem ok1739 : valid D 1739 := by decide +kernel
private theorem ok1740 : valid D 1740 := by decide +kernel
private theorem ok1741 : valid D 1741 := by decide +kernel
private theorem ok1742 : valid D 1742 := by decide +kernel
private theorem ok1743 : valid D 1743 := by decide +kernel
private theorem ok1744 : valid D 1744 := by decide +kernel
private theorem ok1745 : valid D 1745 := by decide +kernel
private theorem ok1746 : valid D 1746 := by decide +kernel
private theorem ok1747 : valid D 1747 := by decide +kernel
private theorem ok1748 : valid D 1748 := by decide +kernel
private theorem ok1749 : valid D 1749 := by decide +kernel
private theorem ok1750 : valid D 1750 := by decide +kernel
private theorem ok1751 : valid D 1751 := by decide +kernel
theorem C1728valid (i : Nat) (_lo : 1728 ≤ i) (_hi : i < 1752) : valid D i := by
  by_cases h1728_1752 : i < 1740
  · by_cases h1728_1740 : i < 1734
    · by_cases h1728_1734 : i < 1731
      · by_cases h1728_1731 : i < 1729
        · have e : i = 1728 := by omega
          subst i
          exact ok1728
        · by_cases h1729_1731 : i < 1730
          · have e : i = 1729 := by omega
            subst i
            exact ok1729
          · have e : i = 1730 := by omega
            subst i
            exact ok1730
      · by_cases h1731_1734 : i < 1732
        · have e : i = 1731 := by omega
          subst i
          exact ok1731
        · by_cases h1732_1734 : i < 1733
          · have e : i = 1732 := by omega
            subst i
            exact ok1732
          · have e : i = 1733 := by omega
            subst i
            exact ok1733
    · by_cases h1734_1740 : i < 1737
      · by_cases h1734_1737 : i < 1735
        · have e : i = 1734 := by omega
          subst i
          exact ok1734
        · by_cases h1735_1737 : i < 1736
          · have e : i = 1735 := by omega
            subst i
            exact ok1735
          · have e : i = 1736 := by omega
            subst i
            exact ok1736
      · by_cases h1737_1740 : i < 1738
        · have e : i = 1737 := by omega
          subst i
          exact ok1737
        · by_cases h1738_1740 : i < 1739
          · have e : i = 1738 := by omega
            subst i
            exact ok1738
          · have e : i = 1739 := by omega
            subst i
            exact ok1739
  · by_cases h1740_1752 : i < 1746
    · by_cases h1740_1746 : i < 1743
      · by_cases h1740_1743 : i < 1741
        · have e : i = 1740 := by omega
          subst i
          exact ok1740
        · by_cases h1741_1743 : i < 1742
          · have e : i = 1741 := by omega
            subst i
            exact ok1741
          · have e : i = 1742 := by omega
            subst i
            exact ok1742
      · by_cases h1743_1746 : i < 1744
        · have e : i = 1743 := by omega
          subst i
          exact ok1743
        · by_cases h1744_1746 : i < 1745
          · have e : i = 1744 := by omega
            subst i
            exact ok1744
          · have e : i = 1745 := by omega
            subst i
            exact ok1745
    · by_cases h1746_1752 : i < 1749
      · by_cases h1746_1749 : i < 1747
        · have e : i = 1746 := by omega
          subst i
          exact ok1746
        · by_cases h1747_1749 : i < 1748
          · have e : i = 1747 := by omega
            subst i
            exact ok1747
          · have e : i = 1748 := by omega
            subst i
            exact ok1748
      · by_cases h1749_1752 : i < 1750
        · have e : i = 1749 := by omega
          subst i
          exact ok1749
        · by_cases h1750_1752 : i < 1751
          · have e : i = 1750 := by omega
            subst i
            exact ok1750
          · have e : i = 1751 := by omega
            subst i
            exact ok1751
end HaarHoneyData
