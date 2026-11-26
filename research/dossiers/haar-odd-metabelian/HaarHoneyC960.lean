import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok960 : valid D 960 := by decide +kernel
private theorem ok961 : valid D 961 := by decide +kernel
private theorem ok962 : valid D 962 := by decide +kernel
private theorem ok963 : valid D 963 := by decide +kernel
private theorem ok964 : valid D 964 := by decide +kernel
private theorem ok965 : valid D 965 := by decide +kernel
private theorem ok966 : valid D 966 := by decide +kernel
private theorem ok967 : valid D 967 := by decide +kernel
private theorem ok968 : valid D 968 := by decide +kernel
private theorem ok969 : valid D 969 := by decide +kernel
private theorem ok970 : valid D 970 := by decide +kernel
private theorem ok971 : valid D 971 := by decide +kernel
private theorem ok972 : valid D 972 := by decide +kernel
private theorem ok973 : valid D 973 := by decide +kernel
private theorem ok974 : valid D 974 := by decide +kernel
private theorem ok975 : valid D 975 := by decide +kernel
private theorem ok976 : valid D 976 := by decide +kernel
private theorem ok977 : valid D 977 := by decide +kernel
private theorem ok978 : valid D 978 := by decide +kernel
private theorem ok979 : valid D 979 := by decide +kernel
private theorem ok980 : valid D 980 := by decide +kernel
private theorem ok981 : valid D 981 := by decide +kernel
private theorem ok982 : valid D 982 := by decide +kernel
private theorem ok983 : valid D 983 := by decide +kernel
theorem C960valid (i : Nat) (_lo : 960 ≤ i) (_hi : i < 984) : valid D i := by
  by_cases h960_984 : i < 972
  · by_cases h960_972 : i < 966
    · by_cases h960_966 : i < 963
      · by_cases h960_963 : i < 961
        · have e : i = 960 := by omega
          subst i
          exact ok960
        · by_cases h961_963 : i < 962
          · have e : i = 961 := by omega
            subst i
            exact ok961
          · have e : i = 962 := by omega
            subst i
            exact ok962
      · by_cases h963_966 : i < 964
        · have e : i = 963 := by omega
          subst i
          exact ok963
        · by_cases h964_966 : i < 965
          · have e : i = 964 := by omega
            subst i
            exact ok964
          · have e : i = 965 := by omega
            subst i
            exact ok965
    · by_cases h966_972 : i < 969
      · by_cases h966_969 : i < 967
        · have e : i = 966 := by omega
          subst i
          exact ok966
        · by_cases h967_969 : i < 968
          · have e : i = 967 := by omega
            subst i
            exact ok967
          · have e : i = 968 := by omega
            subst i
            exact ok968
      · by_cases h969_972 : i < 970
        · have e : i = 969 := by omega
          subst i
          exact ok969
        · by_cases h970_972 : i < 971
          · have e : i = 970 := by omega
            subst i
            exact ok970
          · have e : i = 971 := by omega
            subst i
            exact ok971
  · by_cases h972_984 : i < 978
    · by_cases h972_978 : i < 975
      · by_cases h972_975 : i < 973
        · have e : i = 972 := by omega
          subst i
          exact ok972
        · by_cases h973_975 : i < 974
          · have e : i = 973 := by omega
            subst i
            exact ok973
          · have e : i = 974 := by omega
            subst i
            exact ok974
      · by_cases h975_978 : i < 976
        · have e : i = 975 := by omega
          subst i
          exact ok975
        · by_cases h976_978 : i < 977
          · have e : i = 976 := by omega
            subst i
            exact ok976
          · have e : i = 977 := by omega
            subst i
            exact ok977
    · by_cases h978_984 : i < 981
      · by_cases h978_981 : i < 979
        · have e : i = 978 := by omega
          subst i
          exact ok978
        · by_cases h979_981 : i < 980
          · have e : i = 979 := by omega
            subst i
            exact ok979
          · have e : i = 980 := by omega
            subst i
            exact ok980
      · by_cases h981_984 : i < 982
        · have e : i = 981 := by omega
          subst i
          exact ok981
        · by_cases h982_984 : i < 983
          · have e : i = 982 := by omega
            subst i
            exact ok982
          · have e : i = 983 := by omega
            subst i
            exact ok983
end HaarHoneyData
