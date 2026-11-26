import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok792 : valid D 792 := by decide +kernel
private theorem ok793 : valid D 793 := by decide +kernel
private theorem ok794 : valid D 794 := by decide +kernel
private theorem ok795 : valid D 795 := by decide +kernel
private theorem ok796 : valid D 796 := by decide +kernel
private theorem ok797 : valid D 797 := by decide +kernel
private theorem ok798 : valid D 798 := by decide +kernel
private theorem ok799 : valid D 799 := by decide +kernel
private theorem ok800 : valid D 800 := by decide +kernel
private theorem ok801 : valid D 801 := by decide +kernel
private theorem ok802 : valid D 802 := by decide +kernel
private theorem ok803 : valid D 803 := by decide +kernel
private theorem ok804 : valid D 804 := by decide +kernel
private theorem ok805 : valid D 805 := by decide +kernel
private theorem ok806 : valid D 806 := by decide +kernel
private theorem ok807 : valid D 807 := by decide +kernel
private theorem ok808 : valid D 808 := by decide +kernel
private theorem ok809 : valid D 809 := by decide +kernel
private theorem ok810 : valid D 810 := by decide +kernel
private theorem ok811 : valid D 811 := by decide +kernel
private theorem ok812 : valid D 812 := by decide +kernel
private theorem ok813 : valid D 813 := by decide +kernel
private theorem ok814 : valid D 814 := by decide +kernel
private theorem ok815 : valid D 815 := by decide +kernel
theorem C792valid (i : Nat) (_lo : 792 ≤ i) (_hi : i < 816) : valid D i := by
  by_cases h792_816 : i < 804
  · by_cases h792_804 : i < 798
    · by_cases h792_798 : i < 795
      · by_cases h792_795 : i < 793
        · have e : i = 792 := by omega
          subst i
          exact ok792
        · by_cases h793_795 : i < 794
          · have e : i = 793 := by omega
            subst i
            exact ok793
          · have e : i = 794 := by omega
            subst i
            exact ok794
      · by_cases h795_798 : i < 796
        · have e : i = 795 := by omega
          subst i
          exact ok795
        · by_cases h796_798 : i < 797
          · have e : i = 796 := by omega
            subst i
            exact ok796
          · have e : i = 797 := by omega
            subst i
            exact ok797
    · by_cases h798_804 : i < 801
      · by_cases h798_801 : i < 799
        · have e : i = 798 := by omega
          subst i
          exact ok798
        · by_cases h799_801 : i < 800
          · have e : i = 799 := by omega
            subst i
            exact ok799
          · have e : i = 800 := by omega
            subst i
            exact ok800
      · by_cases h801_804 : i < 802
        · have e : i = 801 := by omega
          subst i
          exact ok801
        · by_cases h802_804 : i < 803
          · have e : i = 802 := by omega
            subst i
            exact ok802
          · have e : i = 803 := by omega
            subst i
            exact ok803
  · by_cases h804_816 : i < 810
    · by_cases h804_810 : i < 807
      · by_cases h804_807 : i < 805
        · have e : i = 804 := by omega
          subst i
          exact ok804
        · by_cases h805_807 : i < 806
          · have e : i = 805 := by omega
            subst i
            exact ok805
          · have e : i = 806 := by omega
            subst i
            exact ok806
      · by_cases h807_810 : i < 808
        · have e : i = 807 := by omega
          subst i
          exact ok807
        · by_cases h808_810 : i < 809
          · have e : i = 808 := by omega
            subst i
            exact ok808
          · have e : i = 809 := by omega
            subst i
            exact ok809
    · by_cases h810_816 : i < 813
      · by_cases h810_813 : i < 811
        · have e : i = 810 := by omega
          subst i
          exact ok810
        · by_cases h811_813 : i < 812
          · have e : i = 811 := by omega
            subst i
            exact ok811
          · have e : i = 812 := by omega
            subst i
            exact ok812
      · by_cases h813_816 : i < 814
        · have e : i = 813 := by omega
          subst i
          exact ok813
        · by_cases h814_816 : i < 815
          · have e : i = 814 := by omega
            subst i
            exact ok814
          · have e : i = 815 := by omega
            subst i
            exact ok815
end HaarHoneyData
