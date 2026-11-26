import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
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
theorem C936valid (i : Nat) (_lo : 936 ≤ i) (_hi : i < 960) : valid D i := by
  by_cases h936_960 : i < 948
  · by_cases h936_948 : i < 942
    · by_cases h936_942 : i < 939
      · by_cases h936_939 : i < 937
        · have e : i = 936 := by omega
          subst i
          exact ok936
        · by_cases h937_939 : i < 938
          · have e : i = 937 := by omega
            subst i
            exact ok937
          · have e : i = 938 := by omega
            subst i
            exact ok938
      · by_cases h939_942 : i < 940
        · have e : i = 939 := by omega
          subst i
          exact ok939
        · by_cases h940_942 : i < 941
          · have e : i = 940 := by omega
            subst i
            exact ok940
          · have e : i = 941 := by omega
            subst i
            exact ok941
    · by_cases h942_948 : i < 945
      · by_cases h942_945 : i < 943
        · have e : i = 942 := by omega
          subst i
          exact ok942
        · by_cases h943_945 : i < 944
          · have e : i = 943 := by omega
            subst i
            exact ok943
          · have e : i = 944 := by omega
            subst i
            exact ok944
      · by_cases h945_948 : i < 946
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
  · by_cases h948_960 : i < 954
    · by_cases h948_954 : i < 951
      · by_cases h948_951 : i < 949
        · have e : i = 948 := by omega
          subst i
          exact ok948
        · by_cases h949_951 : i < 950
          · have e : i = 949 := by omega
            subst i
            exact ok949
          · have e : i = 950 := by omega
            subst i
            exact ok950
      · by_cases h951_954 : i < 952
        · have e : i = 951 := by omega
          subst i
          exact ok951
        · by_cases h952_954 : i < 953
          · have e : i = 952 := by omega
            subst i
            exact ok952
          · have e : i = 953 := by omega
            subst i
            exact ok953
    · by_cases h954_960 : i < 957
      · by_cases h954_957 : i < 955
        · have e : i = 954 := by omega
          subst i
          exact ok954
        · by_cases h955_957 : i < 956
          · have e : i = 955 := by omega
            subst i
            exact ok955
          · have e : i = 956 := by omega
            subst i
            exact ok956
      · by_cases h957_960 : i < 958
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
end HaarHoneyData
