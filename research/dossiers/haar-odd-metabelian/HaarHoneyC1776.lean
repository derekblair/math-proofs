import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1776 : valid D 1776 := by decide +kernel
private theorem ok1777 : valid D 1777 := by decide +kernel
private theorem ok1778 : valid D 1778 := by decide +kernel
private theorem ok1779 : valid D 1779 := by decide +kernel
private theorem ok1780 : valid D 1780 := by decide +kernel
private theorem ok1781 : valid D 1781 := by decide +kernel
private theorem ok1782 : valid D 1782 := by decide +kernel
private theorem ok1783 : valid D 1783 := by decide +kernel
private theorem ok1784 : valid D 1784 := by decide +kernel
private theorem ok1785 : valid D 1785 := by decide +kernel
private theorem ok1786 : valid D 1786 := by decide +kernel
private theorem ok1787 : valid D 1787 := by decide +kernel
private theorem ok1788 : valid D 1788 := by decide +kernel
private theorem ok1789 : valid D 1789 := by decide +kernel
private theorem ok1790 : valid D 1790 := by decide +kernel
private theorem ok1791 : valid D 1791 := by decide +kernel
private theorem ok1792 : valid D 1792 := by decide +kernel
private theorem ok1793 : valid D 1793 := by decide +kernel
private theorem ok1794 : valid D 1794 := by decide +kernel
private theorem ok1795 : valid D 1795 := by decide +kernel
private theorem ok1796 : valid D 1796 := by decide +kernel
theorem C1776valid (i : Nat) (_lo : 1776 ≤ i) (_hi : i < 1797) : valid D i := by
  by_cases h1776_1797 : i < 1786
  · by_cases h1776_1786 : i < 1781
    · by_cases h1776_1781 : i < 1778
      · by_cases h1776_1778 : i < 1777
        · have e : i = 1776 := by omega
          subst i
          exact ok1776
        · have e : i = 1777 := by omega
          subst i
          exact ok1777
      · by_cases h1778_1781 : i < 1779
        · have e : i = 1778 := by omega
          subst i
          exact ok1778
        · by_cases h1779_1781 : i < 1780
          · have e : i = 1779 := by omega
            subst i
            exact ok1779
          · have e : i = 1780 := by omega
            subst i
            exact ok1780
    · by_cases h1781_1786 : i < 1783
      · by_cases h1781_1783 : i < 1782
        · have e : i = 1781 := by omega
          subst i
          exact ok1781
        · have e : i = 1782 := by omega
          subst i
          exact ok1782
      · by_cases h1783_1786 : i < 1784
        · have e : i = 1783 := by omega
          subst i
          exact ok1783
        · by_cases h1784_1786 : i < 1785
          · have e : i = 1784 := by omega
            subst i
            exact ok1784
          · have e : i = 1785 := by omega
            subst i
            exact ok1785
  · by_cases h1786_1797 : i < 1791
    · by_cases h1786_1791 : i < 1788
      · by_cases h1786_1788 : i < 1787
        · have e : i = 1786 := by omega
          subst i
          exact ok1786
        · have e : i = 1787 := by omega
          subst i
          exact ok1787
      · by_cases h1788_1791 : i < 1789
        · have e : i = 1788 := by omega
          subst i
          exact ok1788
        · by_cases h1789_1791 : i < 1790
          · have e : i = 1789 := by omega
            subst i
            exact ok1789
          · have e : i = 1790 := by omega
            subst i
            exact ok1790
    · by_cases h1791_1797 : i < 1794
      · by_cases h1791_1794 : i < 1792
        · have e : i = 1791 := by omega
          subst i
          exact ok1791
        · by_cases h1792_1794 : i < 1793
          · have e : i = 1792 := by omega
            subst i
            exact ok1792
          · have e : i = 1793 := by omega
            subst i
            exact ok1793
      · by_cases h1794_1797 : i < 1795
        · have e : i = 1794 := by omega
          subst i
          exact ok1794
        · by_cases h1795_1797 : i < 1796
          · have e : i = 1795 := by omega
            subst i
            exact ok1795
          · have e : i = 1796 := by omega
            subst i
            exact ok1796
end HaarHoneyData
