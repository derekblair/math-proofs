import HaarMetaTorsionOneData
namespace HaarMetaTorsionOneData
open HaarMetaTorsionOneDAG HaarMetaTorsionOneVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
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
private theorem ok832 : valid D 832 := by decide +kernel
private theorem ok833 : valid D 833 := by decide +kernel
private theorem ok834 : valid D 834 := by decide +kernel
private theorem ok835 : valid D 835 := by decide +kernel
private theorem ok836 : valid D 836 := by decide +kernel
private theorem ok837 : valid D 837 := by decide +kernel
private theorem ok838 : valid D 838 := by decide +kernel
private theorem ok839 : valid D 839 := by decide +kernel
theorem C816valid (i : Nat) (_lo : 816 ≤ i) (_hi : i < 840) : valid D i := by
  by_cases h816_840 : i < 828
  · by_cases h816_828 : i < 822
    · by_cases h816_822 : i < 819
      · by_cases h816_819 : i < 817
        · have e : i = 816 := by omega
          subst i
          exact ok816
        · by_cases h817_819 : i < 818
          · have e : i = 817 := by omega
            subst i
            exact ok817
          · have e : i = 818 := by omega
            subst i
            exact ok818
      · by_cases h819_822 : i < 820
        · have e : i = 819 := by omega
          subst i
          exact ok819
        · by_cases h820_822 : i < 821
          · have e : i = 820 := by omega
            subst i
            exact ok820
          · have e : i = 821 := by omega
            subst i
            exact ok821
    · by_cases h822_828 : i < 825
      · by_cases h822_825 : i < 823
        · have e : i = 822 := by omega
          subst i
          exact ok822
        · by_cases h823_825 : i < 824
          · have e : i = 823 := by omega
            subst i
            exact ok823
          · have e : i = 824 := by omega
            subst i
            exact ok824
      · by_cases h825_828 : i < 826
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
  · by_cases h828_840 : i < 834
    · by_cases h828_834 : i < 831
      · by_cases h828_831 : i < 829
        · have e : i = 828 := by omega
          subst i
          exact ok828
        · by_cases h829_831 : i < 830
          · have e : i = 829 := by omega
            subst i
            exact ok829
          · have e : i = 830 := by omega
            subst i
            exact ok830
      · by_cases h831_834 : i < 832
        · have e : i = 831 := by omega
          subst i
          exact ok831
        · by_cases h832_834 : i < 833
          · have e : i = 832 := by omega
            subst i
            exact ok832
          · have e : i = 833 := by omega
            subst i
            exact ok833
    · by_cases h834_840 : i < 837
      · by_cases h834_837 : i < 835
        · have e : i = 834 := by omega
          subst i
          exact ok834
        · by_cases h835_837 : i < 836
          · have e : i = 835 := by omega
            subst i
            exact ok835
          · have e : i = 836 := by omega
            subst i
            exact ok836
      · by_cases h837_840 : i < 838
        · have e : i = 837 := by omega
          subst i
          exact ok837
        · by_cases h838_840 : i < 839
          · have e : i = 838 := by omega
            subst i
            exact ok838
          · have e : i = 839 := by omega
            subst i
            exact ok839
end HaarMetaTorsionOneData
