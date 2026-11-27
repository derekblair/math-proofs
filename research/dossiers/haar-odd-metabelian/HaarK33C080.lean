import HaarK33Data
namespace HaarK33Data
open HaarK33DAG HaarK33Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
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
theorem C080valid (i : Nat) (_lo : 80 ≤ i) (_hi : i < 96) : valid D i := by
  by_cases h80_96 : i < 88
  · by_cases h80_88 : i < 84
    · by_cases h80_84 : i < 82
      · by_cases h80_82 : i < 81
        · have e : i = 80 := by omega
          subst i
          exact ok80
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
    · by_cases h84_88 : i < 86
      · by_cases h84_86 : i < 85
        · have e : i = 84 := by omega
          subst i
          exact ok84
        · have e : i = 85 := by omega
          subst i
          exact ok85
      · by_cases h86_88 : i < 87
        · have e : i = 86 := by omega
          subst i
          exact ok86
        · have e : i = 87 := by omega
          subst i
          exact ok87
  · by_cases h88_96 : i < 92
    · by_cases h88_92 : i < 90
      · by_cases h88_90 : i < 89
        · have e : i = 88 := by omega
          subst i
          exact ok88
        · have e : i = 89 := by omega
          subst i
          exact ok89
      · by_cases h90_92 : i < 91
        · have e : i = 90 := by omega
          subst i
          exact ok90
        · have e : i = 91 := by omega
          subst i
          exact ok91
    · by_cases h92_96 : i < 94
      · by_cases h92_94 : i < 93
        · have e : i = 92 := by omega
          subst i
          exact ok92
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
end HaarK33Data
