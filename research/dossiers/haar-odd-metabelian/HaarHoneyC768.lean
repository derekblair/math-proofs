import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok768 : valid D 768 := by decide +kernel
private theorem ok769 : valid D 769 := by decide +kernel
private theorem ok770 : valid D 770 := by decide +kernel
private theorem ok771 : valid D 771 := by decide +kernel
private theorem ok772 : valid D 772 := by decide +kernel
private theorem ok773 : valid D 773 := by decide +kernel
private theorem ok774 : valid D 774 := by decide +kernel
private theorem ok775 : valid D 775 := by decide +kernel
private theorem ok776 : valid D 776 := by decide +kernel
private theorem ok777 : valid D 777 := by decide +kernel
private theorem ok778 : valid D 778 := by decide +kernel
private theorem ok779 : valid D 779 := by decide +kernel
private theorem ok780 : valid D 780 := by decide +kernel
private theorem ok781 : valid D 781 := by decide +kernel
private theorem ok782 : valid D 782 := by decide +kernel
private theorem ok783 : valid D 783 := by decide +kernel
private theorem ok784 : valid D 784 := by decide +kernel
private theorem ok785 : valid D 785 := by decide +kernel
private theorem ok786 : valid D 786 := by decide +kernel
private theorem ok787 : valid D 787 := by decide +kernel
private theorem ok788 : valid D 788 := by decide +kernel
private theorem ok789 : valid D 789 := by decide +kernel
private theorem ok790 : valid D 790 := by decide +kernel
private theorem ok791 : valid D 791 := by decide +kernel
theorem C768valid (i : Nat) (_lo : 768 ≤ i) (_hi : i < 792) : valid D i := by
  by_cases h768_792 : i < 780
  · by_cases h768_780 : i < 774
    · by_cases h768_774 : i < 771
      · by_cases h768_771 : i < 769
        · have e : i = 768 := by omega
          subst i
          exact ok768
        · by_cases h769_771 : i < 770
          · have e : i = 769 := by omega
            subst i
            exact ok769
          · have e : i = 770 := by omega
            subst i
            exact ok770
      · by_cases h771_774 : i < 772
        · have e : i = 771 := by omega
          subst i
          exact ok771
        · by_cases h772_774 : i < 773
          · have e : i = 772 := by omega
            subst i
            exact ok772
          · have e : i = 773 := by omega
            subst i
            exact ok773
    · by_cases h774_780 : i < 777
      · by_cases h774_777 : i < 775
        · have e : i = 774 := by omega
          subst i
          exact ok774
        · by_cases h775_777 : i < 776
          · have e : i = 775 := by omega
            subst i
            exact ok775
          · have e : i = 776 := by omega
            subst i
            exact ok776
      · by_cases h777_780 : i < 778
        · have e : i = 777 := by omega
          subst i
          exact ok777
        · by_cases h778_780 : i < 779
          · have e : i = 778 := by omega
            subst i
            exact ok778
          · have e : i = 779 := by omega
            subst i
            exact ok779
  · by_cases h780_792 : i < 786
    · by_cases h780_786 : i < 783
      · by_cases h780_783 : i < 781
        · have e : i = 780 := by omega
          subst i
          exact ok780
        · by_cases h781_783 : i < 782
          · have e : i = 781 := by omega
            subst i
            exact ok781
          · have e : i = 782 := by omega
            subst i
            exact ok782
      · by_cases h783_786 : i < 784
        · have e : i = 783 := by omega
          subst i
          exact ok783
        · by_cases h784_786 : i < 785
          · have e : i = 784 := by omega
            subst i
            exact ok784
          · have e : i = 785 := by omega
            subst i
            exact ok785
    · by_cases h786_792 : i < 789
      · by_cases h786_789 : i < 787
        · have e : i = 786 := by omega
          subst i
          exact ok786
        · by_cases h787_789 : i < 788
          · have e : i = 787 := by omega
            subst i
            exact ok787
          · have e : i = 788 := by omega
            subst i
            exact ok788
      · by_cases h789_792 : i < 790
        · have e : i = 789 := by omega
          subst i
          exact ok789
        · by_cases h790_792 : i < 791
          · have e : i = 790 := by omega
            subst i
            exact ok790
          · have e : i = 791 := by omega
            subst i
            exact ok791
end HaarHoneyData
