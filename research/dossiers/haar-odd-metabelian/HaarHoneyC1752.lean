import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1752 : valid D 1752 := by decide +kernel
private theorem ok1753 : valid D 1753 := by decide +kernel
private theorem ok1754 : valid D 1754 := by decide +kernel
private theorem ok1755 : valid D 1755 := by decide +kernel
private theorem ok1756 : valid D 1756 := by decide +kernel
private theorem ok1757 : valid D 1757 := by decide +kernel
private theorem ok1758 : valid D 1758 := by decide +kernel
private theorem ok1759 : valid D 1759 := by decide +kernel
private theorem ok1760 : valid D 1760 := by decide +kernel
private theorem ok1761 : valid D 1761 := by decide +kernel
private theorem ok1762 : valid D 1762 := by decide +kernel
private theorem ok1763 : valid D 1763 := by decide +kernel
private theorem ok1764 : valid D 1764 := by decide +kernel
private theorem ok1765 : valid D 1765 := by decide +kernel
private theorem ok1766 : valid D 1766 := by decide +kernel
private theorem ok1767 : valid D 1767 := by decide +kernel
private theorem ok1768 : valid D 1768 := by decide +kernel
private theorem ok1769 : valid D 1769 := by decide +kernel
private theorem ok1770 : valid D 1770 := by decide +kernel
private theorem ok1771 : valid D 1771 := by decide +kernel
private theorem ok1772 : valid D 1772 := by decide +kernel
private theorem ok1773 : valid D 1773 := by decide +kernel
private theorem ok1774 : valid D 1774 := by decide +kernel
private theorem ok1775 : valid D 1775 := by decide +kernel
theorem C1752valid (i : Nat) (_lo : 1752 ≤ i) (_hi : i < 1776) : valid D i := by
  by_cases h1752_1776 : i < 1764
  · by_cases h1752_1764 : i < 1758
    · by_cases h1752_1758 : i < 1755
      · by_cases h1752_1755 : i < 1753
        · have e : i = 1752 := by omega
          subst i
          exact ok1752
        · by_cases h1753_1755 : i < 1754
          · have e : i = 1753 := by omega
            subst i
            exact ok1753
          · have e : i = 1754 := by omega
            subst i
            exact ok1754
      · by_cases h1755_1758 : i < 1756
        · have e : i = 1755 := by omega
          subst i
          exact ok1755
        · by_cases h1756_1758 : i < 1757
          · have e : i = 1756 := by omega
            subst i
            exact ok1756
          · have e : i = 1757 := by omega
            subst i
            exact ok1757
    · by_cases h1758_1764 : i < 1761
      · by_cases h1758_1761 : i < 1759
        · have e : i = 1758 := by omega
          subst i
          exact ok1758
        · by_cases h1759_1761 : i < 1760
          · have e : i = 1759 := by omega
            subst i
            exact ok1759
          · have e : i = 1760 := by omega
            subst i
            exact ok1760
      · by_cases h1761_1764 : i < 1762
        · have e : i = 1761 := by omega
          subst i
          exact ok1761
        · by_cases h1762_1764 : i < 1763
          · have e : i = 1762 := by omega
            subst i
            exact ok1762
          · have e : i = 1763 := by omega
            subst i
            exact ok1763
  · by_cases h1764_1776 : i < 1770
    · by_cases h1764_1770 : i < 1767
      · by_cases h1764_1767 : i < 1765
        · have e : i = 1764 := by omega
          subst i
          exact ok1764
        · by_cases h1765_1767 : i < 1766
          · have e : i = 1765 := by omega
            subst i
            exact ok1765
          · have e : i = 1766 := by omega
            subst i
            exact ok1766
      · by_cases h1767_1770 : i < 1768
        · have e : i = 1767 := by omega
          subst i
          exact ok1767
        · by_cases h1768_1770 : i < 1769
          · have e : i = 1768 := by omega
            subst i
            exact ok1768
          · have e : i = 1769 := by omega
            subst i
            exact ok1769
    · by_cases h1770_1776 : i < 1773
      · by_cases h1770_1773 : i < 1771
        · have e : i = 1770 := by omega
          subst i
          exact ok1770
        · by_cases h1771_1773 : i < 1772
          · have e : i = 1771 := by omega
            subst i
            exact ok1771
          · have e : i = 1772 := by omega
            subst i
            exact ok1772
      · by_cases h1773_1776 : i < 1774
        · have e : i = 1773 := by omega
          subst i
          exact ok1773
        · by_cases h1774_1776 : i < 1775
          · have e : i = 1774 := by omega
            subst i
            exact ok1774
          · have e : i = 1775 := by omega
            subst i
            exact ok1775
end HaarHoneyData
