import HaarMetaNineData
namespace HaarMetaNineData
open HaarMetaNineDAG HaarMetaNineVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
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
private theorem ok816 : valid D 816 := by decide +kernel
private theorem ok817 : valid D 817 := by decide +kernel
private theorem ok818 : valid D 818 := by decide +kernel
private theorem ok819 : valid D 819 := by decide +kernel
private theorem ok820 : valid D 820 := by decide +kernel
private theorem ok821 : valid D 821 := by decide +kernel
private theorem ok822 : valid D 822 := by decide +kernel
private theorem ok823 : valid D 823 := by decide +kernel
private theorem ok824 : valid D 824 := by decide +kernel
private theorem ok825 : valid D 825 := by decide +kernel
private theorem ok826 : valid D 826 := by decide +kernel
private theorem ok827 : valid D 827 := by decide +kernel
private theorem ok828 : valid D 828 := by decide +kernel
private theorem ok829 : valid D 829 := by decide +kernel
private theorem ok830 : valid D 830 := by decide +kernel
private theorem ok831 : valid D 831 := by decide +kernel
theorem C800valid (i : Nat) (_lo : 800 ≤ i) (_hi : i < 832) : valid D i := by
  by_cases h800_832 : i < 816
  · by_cases h800_816 : i < 808
    · by_cases h800_808 : i < 804
      · by_cases h800_804 : i < 802
        · by_cases h800_802 : i < 801
          · have e : i = 800 := by omega
            subst i
            exact ok800
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
      · by_cases h804_808 : i < 806
        · by_cases h804_806 : i < 805
          · have e : i = 804 := by omega
            subst i
            exact ok804
          · have e : i = 805 := by omega
            subst i
            exact ok805
        · by_cases h806_808 : i < 807
          · have e : i = 806 := by omega
            subst i
            exact ok806
          · have e : i = 807 := by omega
            subst i
            exact ok807
    · by_cases h808_816 : i < 812
      · by_cases h808_812 : i < 810
        · by_cases h808_810 : i < 809
          · have e : i = 808 := by omega
            subst i
            exact ok808
          · have e : i = 809 := by omega
            subst i
            exact ok809
        · by_cases h810_812 : i < 811
          · have e : i = 810 := by omega
            subst i
            exact ok810
          · have e : i = 811 := by omega
            subst i
            exact ok811
      · by_cases h812_816 : i < 814
        · by_cases h812_814 : i < 813
          · have e : i = 812 := by omega
            subst i
            exact ok812
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
  · by_cases h816_832 : i < 824
    · by_cases h816_824 : i < 820
      · by_cases h816_820 : i < 818
        · by_cases h816_818 : i < 817
          · have e : i = 816 := by omega
            subst i
            exact ok816
          · have e : i = 817 := by omega
            subst i
            exact ok817
        · by_cases h818_820 : i < 819
          · have e : i = 818 := by omega
            subst i
            exact ok818
          · have e : i = 819 := by omega
            subst i
            exact ok819
      · by_cases h820_824 : i < 822
        · by_cases h820_822 : i < 821
          · have e : i = 820 := by omega
            subst i
            exact ok820
          · have e : i = 821 := by omega
            subst i
            exact ok821
        · by_cases h822_824 : i < 823
          · have e : i = 822 := by omega
            subst i
            exact ok822
          · have e : i = 823 := by omega
            subst i
            exact ok823
    · by_cases h824_832 : i < 828
      · by_cases h824_828 : i < 826
        · by_cases h824_826 : i < 825
          · have e : i = 824 := by omega
            subst i
            exact ok824
          · have e : i = 825 := by omega
            subst i
            exact ok825
        · by_cases h826_828 : i < 827
          · have e : i = 826 := by omega
            subst i
            exact ok826
          · have e : i = 827 := by omega
            subst i
            exact ok827
      · by_cases h828_832 : i < 830
        · by_cases h828_830 : i < 829
          · have e : i = 828 := by omega
            subst i
            exact ok828
          · have e : i = 829 := by omega
            subst i
            exact ok829
        · by_cases h830_832 : i < 831
          · have e : i = 830 := by omega
            subst i
            exact ok830
          · have e : i = 831 := by omega
            subst i
            exact ok831
end HaarMetaNineData
