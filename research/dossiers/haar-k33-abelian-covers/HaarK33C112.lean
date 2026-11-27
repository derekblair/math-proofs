import HaarK33Data
namespace HaarK33Data
open HaarK33DAG HaarK33Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok112 : valid D 112 := by decide +kernel
private theorem ok113 : valid D 113 := by decide +kernel
private theorem ok114 : valid D 114 := by decide +kernel
private theorem ok115 : valid D 115 := by decide +kernel
private theorem ok116 : valid D 116 := by decide +kernel
private theorem ok117 : valid D 117 := by decide +kernel
private theorem ok118 : valid D 118 := by decide +kernel
private theorem ok119 : valid D 119 := by decide +kernel
private theorem ok120 : valid D 120 := by decide +kernel
private theorem ok121 : valid D 121 := by decide +kernel
private theorem ok122 : valid D 122 := by decide +kernel
private theorem ok123 : valid D 123 := by decide +kernel
private theorem ok124 : valid D 124 := by decide +kernel
private theorem ok125 : valid D 125 := by decide +kernel
private theorem ok126 : valid D 126 := by decide +kernel
private theorem ok127 : valid D 127 := by decide +kernel
theorem C112valid (i : Nat) (_lo : 112 ≤ i) (_hi : i < 128) : valid D i := by
  by_cases h112_128 : i < 120
  · by_cases h112_120 : i < 116
    · by_cases h112_116 : i < 114
      · by_cases h112_114 : i < 113
        · have e : i = 112 := by omega
          subst i
          exact ok112
        · have e : i = 113 := by omega
          subst i
          exact ok113
      · by_cases h114_116 : i < 115
        · have e : i = 114 := by omega
          subst i
          exact ok114
        · have e : i = 115 := by omega
          subst i
          exact ok115
    · by_cases h116_120 : i < 118
      · by_cases h116_118 : i < 117
        · have e : i = 116 := by omega
          subst i
          exact ok116
        · have e : i = 117 := by omega
          subst i
          exact ok117
      · by_cases h118_120 : i < 119
        · have e : i = 118 := by omega
          subst i
          exact ok118
        · have e : i = 119 := by omega
          subst i
          exact ok119
  · by_cases h120_128 : i < 124
    · by_cases h120_124 : i < 122
      · by_cases h120_122 : i < 121
        · have e : i = 120 := by omega
          subst i
          exact ok120
        · have e : i = 121 := by omega
          subst i
          exact ok121
      · by_cases h122_124 : i < 123
        · have e : i = 122 := by omega
          subst i
          exact ok122
        · have e : i = 123 := by omega
          subst i
          exact ok123
    · by_cases h124_128 : i < 126
      · by_cases h124_126 : i < 125
        · have e : i = 124 := by omega
          subst i
          exact ok124
        · have e : i = 125 := by omega
          subst i
          exact ok125
      · by_cases h126_128 : i < 127
        · have e : i = 126 := by omega
          subst i
          exact ok126
        · have e : i = 127 := by omega
          subst i
          exact ok127
end HaarK33Data
