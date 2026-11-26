import HaarMetaS013Data
namespace HaarMetaS013Data
open HaarMetaS013DAG HaarMetaS013Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok72 : valid D 72 := by decide +kernel
private theorem ok73 : valid D 73 := by decide +kernel
private theorem ok74 : valid D 74 := by decide +kernel
private theorem ok75 : valid D 75 := by decide +kernel
private theorem ok76 : valid D 76 := by decide +kernel
private theorem ok77 : valid D 77 := by decide +kernel
private theorem ok78 : valid D 78 := by decide +kernel
private theorem ok79 : valid D 79 := by decide +kernel
private theorem ok80 : valid D 80 := by decide +kernel
private theorem ok81 : valid D 81 := by decide +kernel
private theorem ok82 : valid D 82 := by decide +kernel
private theorem ok83 : valid D 83 := by decide +kernel
private theorem ok84 : valid D 84 := by decide +kernel
private theorem ok85 : valid D 85 := by decide +kernel
private theorem ok86 : valid D 86 := by decide +kernel
private theorem ok87 : valid D 87 := by decide +kernel
private theorem ok88 : valid D 88 := by decide +kernel
private theorem ok89 : valid D 89 := by decide +kernel
private theorem ok90 : valid D 90 := by decide +kernel
private theorem ok91 : valid D 91 := by decide +kernel
private theorem ok92 : valid D 92 := by decide +kernel
private theorem ok93 : valid D 93 := by decide +kernel
private theorem ok94 : valid D 94 := by decide +kernel
private theorem ok95 : valid D 95 := by decide +kernel
theorem C072valid (i : Nat) (_lo : 72 ≤ i) (_hi : i < 96) : valid D i := by
  by_cases h72_96 : i < 84
  · by_cases h72_84 : i < 78
    · by_cases h72_78 : i < 75
      · by_cases h72_75 : i < 73
        · have e : i = 72 := by omega
          subst i
          exact ok72
        · by_cases h73_75 : i < 74
          · have e : i = 73 := by omega
            subst i
            exact ok73
          · have e : i = 74 := by omega
            subst i
            exact ok74
      · by_cases h75_78 : i < 76
        · have e : i = 75 := by omega
          subst i
          exact ok75
        · by_cases h76_78 : i < 77
          · have e : i = 76 := by omega
            subst i
            exact ok76
          · have e : i = 77 := by omega
            subst i
            exact ok77
    · by_cases h78_84 : i < 81
      · by_cases h78_81 : i < 79
        · have e : i = 78 := by omega
          subst i
          exact ok78
        · by_cases h79_81 : i < 80
          · have e : i = 79 := by omega
            subst i
            exact ok79
          · have e : i = 80 := by omega
            subst i
            exact ok80
      · by_cases h81_84 : i < 82
        · have e : i = 81 := by omega
          subst i
          exact ok81
        · by_cases h82_84 : i < 83
          · have e : i = 82 := by omega
            subst i
            exact ok82
          · have e : i = 83 := by omega
            subst i
            exact ok83
  · by_cases h84_96 : i < 90
    · by_cases h84_90 : i < 87
      · by_cases h84_87 : i < 85
        · have e : i = 84 := by omega
          subst i
          exact ok84
        · by_cases h85_87 : i < 86
          · have e : i = 85 := by omega
            subst i
            exact ok85
          · have e : i = 86 := by omega
            subst i
            exact ok86
      · by_cases h87_90 : i < 88
        · have e : i = 87 := by omega
          subst i
          exact ok87
        · by_cases h88_90 : i < 89
          · have e : i = 88 := by omega
            subst i
            exact ok88
          · have e : i = 89 := by omega
            subst i
            exact ok89
    · by_cases h90_96 : i < 93
      · by_cases h90_93 : i < 91
        · have e : i = 90 := by omega
          subst i
          exact ok90
        · by_cases h91_93 : i < 92
          · have e : i = 91 := by omega
            subst i
            exact ok91
          · have e : i = 92 := by omega
            subst i
            exact ok92
      · by_cases h93_96 : i < 94
        · have e : i = 93 := by omega
          subst i
          exact ok93
        · by_cases h94_96 : i < 95
          · have e : i = 94 := by omega
            subst i
            exact ok94
          · have e : i = 95 := by omega
            subst i
            exact ok95
end HaarMetaS013Data
