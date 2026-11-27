import HaarMetaTorsionOneData
namespace HaarMetaTorsionOneData
open HaarMetaTorsionOneDAG HaarMetaTorsionOneVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok912 : valid D 912 := by decide +kernel
private theorem ok913 : valid D 913 := by decide +kernel
private theorem ok914 : valid D 914 := by decide +kernel
private theorem ok915 : valid D 915 := by decide +kernel
private theorem ok916 : valid D 916 := by decide +kernel
private theorem ok917 : valid D 917 := by decide +kernel
private theorem ok918 : valid D 918 := by decide +kernel
private theorem ok919 : valid D 919 := by decide +kernel
private theorem ok920 : valid D 920 := by decide +kernel
private theorem ok921 : valid D 921 := by decide +kernel
private theorem ok922 : valid D 922 := by decide +kernel
private theorem ok923 : valid D 923 := by decide +kernel
private theorem ok924 : valid D 924 := by decide +kernel
private theorem ok925 : valid D 925 := by decide +kernel
private theorem ok926 : valid D 926 := by decide +kernel
private theorem ok927 : valid D 927 := by decide +kernel
private theorem ok928 : valid D 928 := by decide +kernel
private theorem ok929 : valid D 929 := by decide +kernel
private theorem ok930 : valid D 930 := by decide +kernel
private theorem ok931 : valid D 931 := by decide +kernel
private theorem ok932 : valid D 932 := by decide +kernel
private theorem ok933 : valid D 933 := by decide +kernel
private theorem ok934 : valid D 934 := by decide +kernel
private theorem ok935 : valid D 935 := by decide +kernel
theorem C912valid (i : Nat) (_lo : 912 ≤ i) (_hi : i < 936) : valid D i := by
  by_cases h912_936 : i < 924
  · by_cases h912_924 : i < 918
    · by_cases h912_918 : i < 915
      · by_cases h912_915 : i < 913
        · have e : i = 912 := by omega
          subst i
          exact ok912
        · by_cases h913_915 : i < 914
          · have e : i = 913 := by omega
            subst i
            exact ok913
          · have e : i = 914 := by omega
            subst i
            exact ok914
      · by_cases h915_918 : i < 916
        · have e : i = 915 := by omega
          subst i
          exact ok915
        · by_cases h916_918 : i < 917
          · have e : i = 916 := by omega
            subst i
            exact ok916
          · have e : i = 917 := by omega
            subst i
            exact ok917
    · by_cases h918_924 : i < 921
      · by_cases h918_921 : i < 919
        · have e : i = 918 := by omega
          subst i
          exact ok918
        · by_cases h919_921 : i < 920
          · have e : i = 919 := by omega
            subst i
            exact ok919
          · have e : i = 920 := by omega
            subst i
            exact ok920
      · by_cases h921_924 : i < 922
        · have e : i = 921 := by omega
          subst i
          exact ok921
        · by_cases h922_924 : i < 923
          · have e : i = 922 := by omega
            subst i
            exact ok922
          · have e : i = 923 := by omega
            subst i
            exact ok923
  · by_cases h924_936 : i < 930
    · by_cases h924_930 : i < 927
      · by_cases h924_927 : i < 925
        · have e : i = 924 := by omega
          subst i
          exact ok924
        · by_cases h925_927 : i < 926
          · have e : i = 925 := by omega
            subst i
            exact ok925
          · have e : i = 926 := by omega
            subst i
            exact ok926
      · by_cases h927_930 : i < 928
        · have e : i = 927 := by omega
          subst i
          exact ok927
        · by_cases h928_930 : i < 929
          · have e : i = 928 := by omega
            subst i
            exact ok928
          · have e : i = 929 := by omega
            subst i
            exact ok929
    · by_cases h930_936 : i < 933
      · by_cases h930_933 : i < 931
        · have e : i = 930 := by omega
          subst i
          exact ok930
        · by_cases h931_933 : i < 932
          · have e : i = 931 := by omega
            subst i
            exact ok931
          · have e : i = 932 := by omega
            subst i
            exact ok932
      · by_cases h933_936 : i < 934
        · have e : i = 933 := by omega
          subst i
          exact ok933
        · by_cases h934_936 : i < 935
          · have e : i = 934 := by omega
            subst i
            exact ok934
          · have e : i = 935 := by omega
            subst i
            exact ok935
end HaarMetaTorsionOneData
