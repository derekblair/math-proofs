import HaarMetaNineData
namespace HaarMetaNineData
open HaarMetaNineDAG HaarMetaNineVoltage
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
private theorem ok984 : valid D 984 := by decide +kernel
private theorem ok985 : valid D 985 := by decide +kernel
private theorem ok986 : valid D 986 := by decide +kernel
private theorem ok987 : valid D 987 := by decide +kernel
private theorem ok988 : valid D 988 := by decide +kernel
private theorem ok989 : valid D 989 := by decide +kernel
private theorem ok990 : valid D 990 := by decide +kernel
private theorem ok991 : valid D 991 := by decide +kernel
theorem C960valid (i : Nat) (_lo : 960 ≤ i) (_hi : i < 992) : valid D i := by
  by_cases h960_992 : i < 976
  · by_cases h960_976 : i < 968
    · by_cases h960_968 : i < 964
      · by_cases h960_964 : i < 962
        · by_cases h960_962 : i < 961
          · have e : i = 960 := by omega
            subst i
            exact ok960
          · have e : i = 961 := by omega
            subst i
            exact ok961
        · by_cases h962_964 : i < 963
          · have e : i = 962 := by omega
            subst i
            exact ok962
          · have e : i = 963 := by omega
            subst i
            exact ok963
      · by_cases h964_968 : i < 966
        · by_cases h964_966 : i < 965
          · have e : i = 964 := by omega
            subst i
            exact ok964
          · have e : i = 965 := by omega
            subst i
            exact ok965
        · by_cases h966_968 : i < 967
          · have e : i = 966 := by omega
            subst i
            exact ok966
          · have e : i = 967 := by omega
            subst i
            exact ok967
    · by_cases h968_976 : i < 972
      · by_cases h968_972 : i < 970
        · by_cases h968_970 : i < 969
          · have e : i = 968 := by omega
            subst i
            exact ok968
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
      · by_cases h972_976 : i < 974
        · by_cases h972_974 : i < 973
          · have e : i = 972 := by omega
            subst i
            exact ok972
          · have e : i = 973 := by omega
            subst i
            exact ok973
        · by_cases h974_976 : i < 975
          · have e : i = 974 := by omega
            subst i
            exact ok974
          · have e : i = 975 := by omega
            subst i
            exact ok975
  · by_cases h976_992 : i < 984
    · by_cases h976_984 : i < 980
      · by_cases h976_980 : i < 978
        · by_cases h976_978 : i < 977
          · have e : i = 976 := by omega
            subst i
            exact ok976
          · have e : i = 977 := by omega
            subst i
            exact ok977
        · by_cases h978_980 : i < 979
          · have e : i = 978 := by omega
            subst i
            exact ok978
          · have e : i = 979 := by omega
            subst i
            exact ok979
      · by_cases h980_984 : i < 982
        · by_cases h980_982 : i < 981
          · have e : i = 980 := by omega
            subst i
            exact ok980
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
    · by_cases h984_992 : i < 988
      · by_cases h984_988 : i < 986
        · by_cases h984_986 : i < 985
          · have e : i = 984 := by omega
            subst i
            exact ok984
          · have e : i = 985 := by omega
            subst i
            exact ok985
        · by_cases h986_988 : i < 987
          · have e : i = 986 := by omega
            subst i
            exact ok986
          · have e : i = 987 := by omega
            subst i
            exact ok987
      · by_cases h988_992 : i < 990
        · by_cases h988_990 : i < 989
          · have e : i = 988 := by omega
            subst i
            exact ok988
          · have e : i = 989 := by omega
            subst i
            exact ok989
        · by_cases h990_992 : i < 991
          · have e : i = 990 := by omega
            subst i
            exact ok990
          · have e : i = 991 := by omega
            subst i
            exact ok991
end HaarMetaNineData
