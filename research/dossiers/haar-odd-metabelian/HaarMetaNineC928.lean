import HaarMetaNineData
namespace HaarMetaNineData
open HaarMetaNineDAG HaarMetaNineVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok928 : valid D 928 := by decide +kernel
private theorem ok929 : valid D 929 := by decide +kernel
private theorem ok930 : valid D 930 := by decide +kernel
private theorem ok931 : valid D 931 := by decide +kernel
private theorem ok932 : valid D 932 := by decide +kernel
private theorem ok933 : valid D 933 := by decide +kernel
private theorem ok934 : valid D 934 := by decide +kernel
private theorem ok935 : valid D 935 := by decide +kernel
private theorem ok936 : valid D 936 := by decide +kernel
private theorem ok937 : valid D 937 := by decide +kernel
private theorem ok938 : valid D 938 := by decide +kernel
private theorem ok939 : valid D 939 := by decide +kernel
private theorem ok940 : valid D 940 := by decide +kernel
private theorem ok941 : valid D 941 := by decide +kernel
private theorem ok942 : valid D 942 := by decide +kernel
private theorem ok943 : valid D 943 := by decide +kernel
private theorem ok944 : valid D 944 := by decide +kernel
private theorem ok945 : valid D 945 := by decide +kernel
private theorem ok946 : valid D 946 := by decide +kernel
private theorem ok947 : valid D 947 := by decide +kernel
private theorem ok948 : valid D 948 := by decide +kernel
private theorem ok949 : valid D 949 := by decide +kernel
private theorem ok950 : valid D 950 := by decide +kernel
private theorem ok951 : valid D 951 := by decide +kernel
private theorem ok952 : valid D 952 := by decide +kernel
private theorem ok953 : valid D 953 := by decide +kernel
private theorem ok954 : valid D 954 := by decide +kernel
private theorem ok955 : valid D 955 := by decide +kernel
private theorem ok956 : valid D 956 := by decide +kernel
private theorem ok957 : valid D 957 := by decide +kernel
private theorem ok958 : valid D 958 := by decide +kernel
private theorem ok959 : valid D 959 := by decide +kernel
theorem C928valid (i : Nat) (_lo : 928 ≤ i) (_hi : i < 960) : valid D i := by
  by_cases h928_960 : i < 944
  · by_cases h928_944 : i < 936
    · by_cases h928_936 : i < 932
      · by_cases h928_932 : i < 930
        · by_cases h928_930 : i < 929
          · have e : i = 928 := by omega
            subst i
            exact ok928
          · have e : i = 929 := by omega
            subst i
            exact ok929
        · by_cases h930_932 : i < 931
          · have e : i = 930 := by omega
            subst i
            exact ok930
          · have e : i = 931 := by omega
            subst i
            exact ok931
      · by_cases h932_936 : i < 934
        · by_cases h932_934 : i < 933
          · have e : i = 932 := by omega
            subst i
            exact ok932
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
    · by_cases h936_944 : i < 940
      · by_cases h936_940 : i < 938
        · by_cases h936_938 : i < 937
          · have e : i = 936 := by omega
            subst i
            exact ok936
          · have e : i = 937 := by omega
            subst i
            exact ok937
        · by_cases h938_940 : i < 939
          · have e : i = 938 := by omega
            subst i
            exact ok938
          · have e : i = 939 := by omega
            subst i
            exact ok939
      · by_cases h940_944 : i < 942
        · by_cases h940_942 : i < 941
          · have e : i = 940 := by omega
            subst i
            exact ok940
          · have e : i = 941 := by omega
            subst i
            exact ok941
        · by_cases h942_944 : i < 943
          · have e : i = 942 := by omega
            subst i
            exact ok942
          · have e : i = 943 := by omega
            subst i
            exact ok943
  · by_cases h944_960 : i < 952
    · by_cases h944_952 : i < 948
      · by_cases h944_948 : i < 946
        · by_cases h944_946 : i < 945
          · have e : i = 944 := by omega
            subst i
            exact ok944
          · have e : i = 945 := by omega
            subst i
            exact ok945
        · by_cases h946_948 : i < 947
          · have e : i = 946 := by omega
            subst i
            exact ok946
          · have e : i = 947 := by omega
            subst i
            exact ok947
      · by_cases h948_952 : i < 950
        · by_cases h948_950 : i < 949
          · have e : i = 948 := by omega
            subst i
            exact ok948
          · have e : i = 949 := by omega
            subst i
            exact ok949
        · by_cases h950_952 : i < 951
          · have e : i = 950 := by omega
            subst i
            exact ok950
          · have e : i = 951 := by omega
            subst i
            exact ok951
    · by_cases h952_960 : i < 956
      · by_cases h952_956 : i < 954
        · by_cases h952_954 : i < 953
          · have e : i = 952 := by omega
            subst i
            exact ok952
          · have e : i = 953 := by omega
            subst i
            exact ok953
        · by_cases h954_956 : i < 955
          · have e : i = 954 := by omega
            subst i
            exact ok954
          · have e : i = 955 := by omega
            subst i
            exact ok955
      · by_cases h956_960 : i < 958
        · by_cases h956_958 : i < 957
          · have e : i = 956 := by omega
            subst i
            exact ok956
          · have e : i = 957 := by omega
            subst i
            exact ok957
        · by_cases h958_960 : i < 959
          · have e : i = 958 := by omega
            subst i
            exact ok958
          · have e : i = 959 := by omega
            subst i
            exact ok959
end HaarMetaNineData
