import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1032 : valid D 1032 := by decide +kernel
private theorem ok1033 : valid D 1033 := by decide +kernel
private theorem ok1034 : valid D 1034 := by decide +kernel
private theorem ok1035 : valid D 1035 := by decide +kernel
private theorem ok1036 : valid D 1036 := by decide +kernel
private theorem ok1037 : valid D 1037 := by decide +kernel
private theorem ok1038 : valid D 1038 := by decide +kernel
private theorem ok1039 : valid D 1039 := by decide +kernel
private theorem ok1040 : valid D 1040 := by decide +kernel
private theorem ok1041 : valid D 1041 := by decide +kernel
private theorem ok1042 : valid D 1042 := by decide +kernel
private theorem ok1043 : valid D 1043 := by decide +kernel
private theorem ok1044 : valid D 1044 := by decide +kernel
private theorem ok1045 : valid D 1045 := by decide +kernel
private theorem ok1046 : valid D 1046 := by decide +kernel
private theorem ok1047 : valid D 1047 := by decide +kernel
private theorem ok1048 : valid D 1048 := by decide +kernel
private theorem ok1049 : valid D 1049 := by decide +kernel
private theorem ok1050 : valid D 1050 := by decide +kernel
private theorem ok1051 : valid D 1051 := by decide +kernel
private theorem ok1052 : valid D 1052 := by decide +kernel
private theorem ok1053 : valid D 1053 := by decide +kernel
private theorem ok1054 : valid D 1054 := by decide +kernel
private theorem ok1055 : valid D 1055 := by decide +kernel
theorem C1032valid (i : Nat) (_lo : 1032 ≤ i) (_hi : i < 1056) : valid D i := by
  by_cases h1032_1056 : i < 1044
  · by_cases h1032_1044 : i < 1038
    · by_cases h1032_1038 : i < 1035
      · by_cases h1032_1035 : i < 1033
        · have e : i = 1032 := by omega
          subst i
          exact ok1032
        · by_cases h1033_1035 : i < 1034
          · have e : i = 1033 := by omega
            subst i
            exact ok1033
          · have e : i = 1034 := by omega
            subst i
            exact ok1034
      · by_cases h1035_1038 : i < 1036
        · have e : i = 1035 := by omega
          subst i
          exact ok1035
        · by_cases h1036_1038 : i < 1037
          · have e : i = 1036 := by omega
            subst i
            exact ok1036
          · have e : i = 1037 := by omega
            subst i
            exact ok1037
    · by_cases h1038_1044 : i < 1041
      · by_cases h1038_1041 : i < 1039
        · have e : i = 1038 := by omega
          subst i
          exact ok1038
        · by_cases h1039_1041 : i < 1040
          · have e : i = 1039 := by omega
            subst i
            exact ok1039
          · have e : i = 1040 := by omega
            subst i
            exact ok1040
      · by_cases h1041_1044 : i < 1042
        · have e : i = 1041 := by omega
          subst i
          exact ok1041
        · by_cases h1042_1044 : i < 1043
          · have e : i = 1042 := by omega
            subst i
            exact ok1042
          · have e : i = 1043 := by omega
            subst i
            exact ok1043
  · by_cases h1044_1056 : i < 1050
    · by_cases h1044_1050 : i < 1047
      · by_cases h1044_1047 : i < 1045
        · have e : i = 1044 := by omega
          subst i
          exact ok1044
        · by_cases h1045_1047 : i < 1046
          · have e : i = 1045 := by omega
            subst i
            exact ok1045
          · have e : i = 1046 := by omega
            subst i
            exact ok1046
      · by_cases h1047_1050 : i < 1048
        · have e : i = 1047 := by omega
          subst i
          exact ok1047
        · by_cases h1048_1050 : i < 1049
          · have e : i = 1048 := by omega
            subst i
            exact ok1048
          · have e : i = 1049 := by omega
            subst i
            exact ok1049
    · by_cases h1050_1056 : i < 1053
      · by_cases h1050_1053 : i < 1051
        · have e : i = 1050 := by omega
          subst i
          exact ok1050
        · by_cases h1051_1053 : i < 1052
          · have e : i = 1051 := by omega
            subst i
            exact ok1051
          · have e : i = 1052 := by omega
            subst i
            exact ok1052
      · by_cases h1053_1056 : i < 1054
        · have e : i = 1053 := by omega
          subst i
          exact ok1053
        · by_cases h1054_1056 : i < 1055
          · have e : i = 1054 := by omega
            subst i
            exact ok1054
          · have e : i = 1055 := by omega
            subst i
            exact ok1055
end HaarHoneyData
