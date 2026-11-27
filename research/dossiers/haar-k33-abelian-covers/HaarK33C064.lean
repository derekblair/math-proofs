import HaarK33Data
namespace HaarK33Data
open HaarK33DAG HaarK33Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok64 : valid D 64 := by decide +kernel
private theorem ok65 : valid D 65 := by decide +kernel
private theorem ok66 : valid D 66 := by decide +kernel
private theorem ok67 : valid D 67 := by decide +kernel
private theorem ok68 : valid D 68 := by decide +kernel
private theorem ok69 : valid D 69 := by decide +kernel
private theorem ok70 : valid D 70 := by decide +kernel
private theorem ok71 : valid D 71 := by decide +kernel
private theorem ok72 : valid D 72 := by decide +kernel
private theorem ok73 : valid D 73 := by decide +kernel
private theorem ok74 : valid D 74 := by decide +kernel
private theorem ok75 : valid D 75 := by decide +kernel
private theorem ok76 : valid D 76 := by decide +kernel
private theorem ok77 : valid D 77 := by decide +kernel
private theorem ok78 : valid D 78 := by decide +kernel
private theorem ok79 : valid D 79 := by decide +kernel
theorem C064valid (i : Nat) (_lo : 64 ≤ i) (_hi : i < 80) : valid D i := by
  by_cases h64_80 : i < 72
  · by_cases h64_72 : i < 68
    · by_cases h64_68 : i < 66
      · by_cases h64_66 : i < 65
        · have e : i = 64 := by omega
          subst i
          exact ok64
        · have e : i = 65 := by omega
          subst i
          exact ok65
      · by_cases h66_68 : i < 67
        · have e : i = 66 := by omega
          subst i
          exact ok66
        · have e : i = 67 := by omega
          subst i
          exact ok67
    · by_cases h68_72 : i < 70
      · by_cases h68_70 : i < 69
        · have e : i = 68 := by omega
          subst i
          exact ok68
        · have e : i = 69 := by omega
          subst i
          exact ok69
      · by_cases h70_72 : i < 71
        · have e : i = 70 := by omega
          subst i
          exact ok70
        · have e : i = 71 := by omega
          subst i
          exact ok71
  · by_cases h72_80 : i < 76
    · by_cases h72_76 : i < 74
      · by_cases h72_74 : i < 73
        · have e : i = 72 := by omega
          subst i
          exact ok72
        · have e : i = 73 := by omega
          subst i
          exact ok73
      · by_cases h74_76 : i < 75
        · have e : i = 74 := by omega
          subst i
          exact ok74
        · have e : i = 75 := by omega
          subst i
          exact ok75
    · by_cases h76_80 : i < 78
      · by_cases h76_78 : i < 77
        · have e : i = 76 := by omega
          subst i
          exact ok76
        · have e : i = 77 := by omega
          subst i
          exact ok77
      · by_cases h78_80 : i < 79
        · have e : i = 78 := by omega
          subst i
          exact ok78
        · have e : i = 79 := by omega
          subst i
          exact ok79
end HaarK33Data
