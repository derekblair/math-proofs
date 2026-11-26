import HaarMetaNineData
namespace HaarMetaNineData
open HaarMetaNineDAG HaarMetaNineVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
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
theorem C896valid (i : Nat) (_lo : 896 ≤ i) (_hi : i < 928) : valid D i := by
  by_cases h896_928 : i < 912
  · by_cases h896_912 : i < 904
    · by_cases h896_904 : i < 900
      · by_cases h896_900 : i < 898
        · by_cases h896_898 : i < 897
          · have e : i = 896 := by omega
            subst i
            exact ok896
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
      · by_cases h900_904 : i < 902
        · by_cases h900_902 : i < 901
          · have e : i = 900 := by omega
            subst i
            exact ok900
          · have e : i = 901 := by omega
            subst i
            exact ok901
        · by_cases h902_904 : i < 903
          · have e : i = 902 := by omega
            subst i
            exact ok902
          · have e : i = 903 := by omega
            subst i
            exact ok903
    · by_cases h904_912 : i < 908
      · by_cases h904_908 : i < 906
        · by_cases h904_906 : i < 905
          · have e : i = 904 := by omega
            subst i
            exact ok904
          · have e : i = 905 := by omega
            subst i
            exact ok905
        · by_cases h906_908 : i < 907
          · have e : i = 906 := by omega
            subst i
            exact ok906
          · have e : i = 907 := by omega
            subst i
            exact ok907
      · by_cases h908_912 : i < 910
        · by_cases h908_910 : i < 909
          · have e : i = 908 := by omega
            subst i
            exact ok908
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
  · by_cases h912_928 : i < 920
    · by_cases h912_920 : i < 916
      · by_cases h912_916 : i < 914
        · by_cases h912_914 : i < 913
          · have e : i = 912 := by omega
            subst i
            exact ok912
          · have e : i = 913 := by omega
            subst i
            exact ok913
        · by_cases h914_916 : i < 915
          · have e : i = 914 := by omega
            subst i
            exact ok914
          · have e : i = 915 := by omega
            subst i
            exact ok915
      · by_cases h916_920 : i < 918
        · by_cases h916_918 : i < 917
          · have e : i = 916 := by omega
            subst i
            exact ok916
          · have e : i = 917 := by omega
            subst i
            exact ok917
        · by_cases h918_920 : i < 919
          · have e : i = 918 := by omega
            subst i
            exact ok918
          · have e : i = 919 := by omega
            subst i
            exact ok919
    · by_cases h920_928 : i < 924
      · by_cases h920_924 : i < 922
        · by_cases h920_922 : i < 921
          · have e : i = 920 := by omega
            subst i
            exact ok920
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
      · by_cases h924_928 : i < 926
        · by_cases h924_926 : i < 925
          · have e : i = 924 := by omega
            subst i
            exact ok924
          · have e : i = 925 := by omega
            subst i
            exact ok925
        · by_cases h926_928 : i < 927
          · have e : i = 926 := by omega
            subst i
            exact ok926
          · have e : i = 927 := by omega
            subst i
            exact ok927
end HaarMetaNineData
