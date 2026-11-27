import HaarMetaTorsionOneData
namespace HaarMetaTorsionOneData
open HaarMetaTorsionOneDAG HaarMetaTorsionOneVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok888 : valid D 888 := by decide +kernel
private theorem ok889 : valid D 889 := by decide +kernel
private theorem ok890 : valid D 890 := by decide +kernel
private theorem ok891 : valid D 891 := by decide +kernel
private theorem ok892 : valid D 892 := by decide +kernel
private theorem ok893 : valid D 893 := by decide +kernel
private theorem ok894 : valid D 894 := by decide +kernel
private theorem ok895 : valid D 895 := by decide +kernel
private theorem ok896 : valid D 896 := by decide +kernel
private theorem ok897 : valid D 897 := by decide +kernel
private theorem ok898 : valid D 898 := by decide +kernel
private theorem ok899 : valid D 899 := by decide +kernel
private theorem ok900 : valid D 900 := by decide +kernel
private theorem ok901 : valid D 901 := by decide +kernel
private theorem ok902 : valid D 902 := by decide +kernel
private theorem ok903 : valid D 903 := by decide +kernel
private theorem ok904 : valid D 904 := by decide +kernel
private theorem ok905 : valid D 905 := by decide +kernel
private theorem ok906 : valid D 906 := by decide +kernel
private theorem ok907 : valid D 907 := by decide +kernel
private theorem ok908 : valid D 908 := by decide +kernel
private theorem ok909 : valid D 909 := by decide +kernel
private theorem ok910 : valid D 910 := by decide +kernel
private theorem ok911 : valid D 911 := by decide +kernel
theorem C888valid (i : Nat) (_lo : 888 ≤ i) (_hi : i < 912) : valid D i := by
  by_cases h888_912 : i < 900
  · by_cases h888_900 : i < 894
    · by_cases h888_894 : i < 891
      · by_cases h888_891 : i < 889
        · have e : i = 888 := by omega
          subst i
          exact ok888
        · by_cases h889_891 : i < 890
          · have e : i = 889 := by omega
            subst i
            exact ok889
          · have e : i = 890 := by omega
            subst i
            exact ok890
      · by_cases h891_894 : i < 892
        · have e : i = 891 := by omega
          subst i
          exact ok891
        · by_cases h892_894 : i < 893
          · have e : i = 892 := by omega
            subst i
            exact ok892
          · have e : i = 893 := by omega
            subst i
            exact ok893
    · by_cases h894_900 : i < 897
      · by_cases h894_897 : i < 895
        · have e : i = 894 := by omega
          subst i
          exact ok894
        · by_cases h895_897 : i < 896
          · have e : i = 895 := by omega
            subst i
            exact ok895
          · have e : i = 896 := by omega
            subst i
            exact ok896
      · by_cases h897_900 : i < 898
        · have e : i = 897 := by omega
          subst i
          exact ok897
        · by_cases h898_900 : i < 899
          · have e : i = 898 := by omega
            subst i
            exact ok898
          · have e : i = 899 := by omega
            subst i
            exact ok899
  · by_cases h900_912 : i < 906
    · by_cases h900_906 : i < 903
      · by_cases h900_903 : i < 901
        · have e : i = 900 := by omega
          subst i
          exact ok900
        · by_cases h901_903 : i < 902
          · have e : i = 901 := by omega
            subst i
            exact ok901
          · have e : i = 902 := by omega
            subst i
            exact ok902
      · by_cases h903_906 : i < 904
        · have e : i = 903 := by omega
          subst i
          exact ok903
        · by_cases h904_906 : i < 905
          · have e : i = 904 := by omega
            subst i
            exact ok904
          · have e : i = 905 := by omega
            subst i
            exact ok905
    · by_cases h906_912 : i < 909
      · by_cases h906_909 : i < 907
        · have e : i = 906 := by omega
          subst i
          exact ok906
        · by_cases h907_909 : i < 908
          · have e : i = 907 := by omega
            subst i
            exact ok907
          · have e : i = 908 := by omega
            subst i
            exact ok908
      · by_cases h909_912 : i < 910
        · have e : i = 909 := by omega
          subst i
          exact ok909
        · by_cases h910_912 : i < 911
          · have e : i = 910 := by omega
            subst i
            exact ok910
          · have e : i = 911 := by omega
            subst i
            exact ok911
end HaarMetaTorsionOneData
