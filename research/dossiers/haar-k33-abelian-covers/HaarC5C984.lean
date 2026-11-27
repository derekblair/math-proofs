import HaarC5Data
namespace HaarC5Data
open HaarC5DAG HaarC5Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok984 : valid D 984 := by decide +kernel
private theorem ok985 : valid D 985 := by decide +kernel
private theorem ok986 : valid D 986 := by decide +kernel
private theorem ok987 : valid D 987 := by decide +kernel
private theorem ok988 : valid D 988 := by decide +kernel
private theorem ok989 : valid D 989 := by decide +kernel
private theorem ok990 : valid D 990 := by decide +kernel
private theorem ok991 : valid D 991 := by decide +kernel
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
theorem C984valid (i : Nat) (_lo : 984 ≤ i) (_hi : i < 1008) : valid D i := by
  by_cases h984_1008 : i < 996
  · by_cases h984_996 : i < 990
    · by_cases h984_990 : i < 987
      · by_cases h984_987 : i < 985
        · have e : i = 984 := by omega
          subst i
          exact ok984
        · by_cases h985_987 : i < 986
          · have e : i = 985 := by omega
            subst i
            exact ok985
          · have e : i = 986 := by omega
            subst i
            exact ok986
      · by_cases h987_990 : i < 988
        · have e : i = 987 := by omega
          subst i
          exact ok987
        · by_cases h988_990 : i < 989
          · have e : i = 988 := by omega
            subst i
            exact ok988
          · have e : i = 989 := by omega
            subst i
            exact ok989
    · by_cases h990_996 : i < 993
      · by_cases h990_993 : i < 991
        · have e : i = 990 := by omega
          subst i
          exact ok990
        · by_cases h991_993 : i < 992
          · have e : i = 991 := by omega
            subst i
            exact ok991
          · have e : i = 992 := by omega
            subst i
            exact ok992
      · by_cases h993_996 : i < 994
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
  · by_cases h996_1008 : i < 1002
    · by_cases h996_1002 : i < 999
      · by_cases h996_999 : i < 997
        · have e : i = 996 := by omega
          subst i
          exact ok996
        · by_cases h997_999 : i < 998
          · have e : i = 997 := by omega
            subst i
            exact ok997
          · have e : i = 998 := by omega
            subst i
            exact ok998
      · by_cases h999_1002 : i < 1000
        · have e : i = 999 := by omega
          subst i
          exact ok999
        · by_cases h1000_1002 : i < 1001
          · have e : i = 1000 := by omega
            subst i
            exact ok1000
          · have e : i = 1001 := by omega
            subst i
            exact ok1001
    · by_cases h1002_1008 : i < 1005
      · by_cases h1002_1005 : i < 1003
        · have e : i = 1002 := by omega
          subst i
          exact ok1002
        · by_cases h1003_1005 : i < 1004
          · have e : i = 1003 := by omega
            subst i
            exact ok1003
          · have e : i = 1004 := by omega
            subst i
            exact ok1004
      · by_cases h1005_1008 : i < 1006
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
end HaarC5Data
