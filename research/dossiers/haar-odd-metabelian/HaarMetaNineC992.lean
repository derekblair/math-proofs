import HaarMetaNineData
namespace HaarMetaNineData
open HaarMetaNineDAG HaarMetaNineVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok992 : valid D 992 := by decide +kernel
private theorem ok993 : valid D 993 := by decide +kernel
private theorem ok994 : valid D 994 := by decide +kernel
private theorem ok995 : valid D 995 := by decide +kernel
private theorem ok996 : valid D 996 := by decide +kernel
private theorem ok997 : valid D 997 := by decide +kernel
private theorem ok998 : valid D 998 := by decide +kernel
private theorem ok999 : valid D 999 := by decide +kernel
private theorem ok1000 : valid D 1000 := by decide +kernel
private theorem ok1001 : valid D 1001 := by decide +kernel
private theorem ok1002 : valid D 1002 := by decide +kernel
private theorem ok1003 : valid D 1003 := by decide +kernel
private theorem ok1004 : valid D 1004 := by decide +kernel
private theorem ok1005 : valid D 1005 := by decide +kernel
private theorem ok1006 : valid D 1006 := by decide +kernel
private theorem ok1007 : valid D 1007 := by decide +kernel
private theorem ok1008 : valid D 1008 := by decide +kernel
private theorem ok1009 : valid D 1009 := by decide +kernel
private theorem ok1010 : valid D 1010 := by decide +kernel
private theorem ok1011 : valid D 1011 := by decide +kernel
private theorem ok1012 : valid D 1012 := by decide +kernel
private theorem ok1013 : valid D 1013 := by decide +kernel
private theorem ok1014 : valid D 1014 := by decide +kernel
private theorem ok1015 : valid D 1015 := by decide +kernel
private theorem ok1016 : valid D 1016 := by decide +kernel
private theorem ok1017 : valid D 1017 := by decide +kernel
private theorem ok1018 : valid D 1018 := by decide +kernel
private theorem ok1019 : valid D 1019 := by decide +kernel
private theorem ok1020 : valid D 1020 := by decide +kernel
private theorem ok1021 : valid D 1021 := by decide +kernel
private theorem ok1022 : valid D 1022 := by decide +kernel
private theorem ok1023 : valid D 1023 := by decide +kernel
theorem C992valid (i : Nat) (_lo : 992 ≤ i) (_hi : i < 1024) : valid D i := by
  by_cases h992_1024 : i < 1008
  · by_cases h992_1008 : i < 1000
    · by_cases h992_1000 : i < 996
      · by_cases h992_996 : i < 994
        · by_cases h992_994 : i < 993
          · have e : i = 992 := by omega
            subst i
            exact ok992
          · have e : i = 993 := by omega
            subst i
            exact ok993
        · by_cases h994_996 : i < 995
          · have e : i = 994 := by omega
            subst i
            exact ok994
          · have e : i = 995 := by omega
            subst i
            exact ok995
      · by_cases h996_1000 : i < 998
        · by_cases h996_998 : i < 997
          · have e : i = 996 := by omega
            subst i
            exact ok996
          · have e : i = 997 := by omega
            subst i
            exact ok997
        · by_cases h998_1000 : i < 999
          · have e : i = 998 := by omega
            subst i
            exact ok998
          · have e : i = 999 := by omega
            subst i
            exact ok999
    · by_cases h1000_1008 : i < 1004
      · by_cases h1000_1004 : i < 1002
        · by_cases h1000_1002 : i < 1001
          · have e : i = 1000 := by omega
            subst i
            exact ok1000
          · have e : i = 1001 := by omega
            subst i
            exact ok1001
        · by_cases h1002_1004 : i < 1003
          · have e : i = 1002 := by omega
            subst i
            exact ok1002
          · have e : i = 1003 := by omega
            subst i
            exact ok1003
      · by_cases h1004_1008 : i < 1006
        · by_cases h1004_1006 : i < 1005
          · have e : i = 1004 := by omega
            subst i
            exact ok1004
          · have e : i = 1005 := by omega
            subst i
            exact ok1005
        · by_cases h1006_1008 : i < 1007
          · have e : i = 1006 := by omega
            subst i
            exact ok1006
          · have e : i = 1007 := by omega
            subst i
            exact ok1007
  · by_cases h1008_1024 : i < 1016
    · by_cases h1008_1016 : i < 1012
      · by_cases h1008_1012 : i < 1010
        · by_cases h1008_1010 : i < 1009
          · have e : i = 1008 := by omega
            subst i
            exact ok1008
          · have e : i = 1009 := by omega
            subst i
            exact ok1009
        · by_cases h1010_1012 : i < 1011
          · have e : i = 1010 := by omega
            subst i
            exact ok1010
          · have e : i = 1011 := by omega
            subst i
            exact ok1011
      · by_cases h1012_1016 : i < 1014
        · by_cases h1012_1014 : i < 1013
          · have e : i = 1012 := by omega
            subst i
            exact ok1012
          · have e : i = 1013 := by omega
            subst i
            exact ok1013
        · by_cases h1014_1016 : i < 1015
          · have e : i = 1014 := by omega
            subst i
            exact ok1014
          · have e : i = 1015 := by omega
            subst i
            exact ok1015
    · by_cases h1016_1024 : i < 1020
      · by_cases h1016_1020 : i < 1018
        · by_cases h1016_1018 : i < 1017
          · have e : i = 1016 := by omega
            subst i
            exact ok1016
          · have e : i = 1017 := by omega
            subst i
            exact ok1017
        · by_cases h1018_1020 : i < 1019
          · have e : i = 1018 := by omega
            subst i
            exact ok1018
          · have e : i = 1019 := by omega
            subst i
            exact ok1019
      · by_cases h1020_1024 : i < 1022
        · by_cases h1020_1022 : i < 1021
          · have e : i = 1020 := by omega
            subst i
            exact ok1020
          · have e : i = 1021 := by omega
            subst i
            exact ok1021
        · by_cases h1022_1024 : i < 1023
          · have e : i = 1022 := by omega
            subst i
            exact ok1022
          · have e : i = 1023 := by omega
            subst i
            exact ok1023
end HaarMetaNineData
