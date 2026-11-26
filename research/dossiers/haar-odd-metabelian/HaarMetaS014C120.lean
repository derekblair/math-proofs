import HaarMetaS014Data
namespace HaarMetaS014Data
open HaarMetaS014DAG HaarMetaS014Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok120 : valid D 120 := by decide +kernel
private theorem ok121 : valid D 121 := by decide +kernel
private theorem ok122 : valid D 122 := by decide +kernel
private theorem ok123 : valid D 123 := by decide +kernel
private theorem ok124 : valid D 124 := by decide +kernel
private theorem ok125 : valid D 125 := by decide +kernel
private theorem ok126 : valid D 126 := by decide +kernel
private theorem ok127 : valid D 127 := by decide +kernel
private theorem ok128 : valid D 128 := by decide +kernel
private theorem ok129 : valid D 129 := by decide +kernel
private theorem ok130 : valid D 130 := by decide +kernel
private theorem ok131 : valid D 131 := by decide +kernel
private theorem ok132 : valid D 132 := by decide +kernel
private theorem ok133 : valid D 133 := by decide +kernel
private theorem ok134 : valid D 134 := by decide +kernel
private theorem ok135 : valid D 135 := by decide +kernel
private theorem ok136 : valid D 136 := by decide +kernel
private theorem ok137 : valid D 137 := by decide +kernel
private theorem ok138 : valid D 138 := by decide +kernel
private theorem ok139 : valid D 139 := by decide +kernel
private theorem ok140 : valid D 140 := by decide +kernel
private theorem ok141 : valid D 141 := by decide +kernel
private theorem ok142 : valid D 142 := by decide +kernel
private theorem ok143 : valid D 143 := by decide +kernel
theorem C120valid (i : Nat) (_lo : 120 ≤ i) (_hi : i < 144) : valid D i := by
  by_cases h120_144 : i < 132
  · by_cases h120_132 : i < 126
    · by_cases h120_126 : i < 123
      · by_cases h120_123 : i < 121
        · have e : i = 120 := by omega
          subst i
          exact ok120
        · by_cases h121_123 : i < 122
          · have e : i = 121 := by omega
            subst i
            exact ok121
          · have e : i = 122 := by omega
            subst i
            exact ok122
      · by_cases h123_126 : i < 124
        · have e : i = 123 := by omega
          subst i
          exact ok123
        · by_cases h124_126 : i < 125
          · have e : i = 124 := by omega
            subst i
            exact ok124
          · have e : i = 125 := by omega
            subst i
            exact ok125
    · by_cases h126_132 : i < 129
      · by_cases h126_129 : i < 127
        · have e : i = 126 := by omega
          subst i
          exact ok126
        · by_cases h127_129 : i < 128
          · have e : i = 127 := by omega
            subst i
            exact ok127
          · have e : i = 128 := by omega
            subst i
            exact ok128
      · by_cases h129_132 : i < 130
        · have e : i = 129 := by omega
          subst i
          exact ok129
        · by_cases h130_132 : i < 131
          · have e : i = 130 := by omega
            subst i
            exact ok130
          · have e : i = 131 := by omega
            subst i
            exact ok131
  · by_cases h132_144 : i < 138
    · by_cases h132_138 : i < 135
      · by_cases h132_135 : i < 133
        · have e : i = 132 := by omega
          subst i
          exact ok132
        · by_cases h133_135 : i < 134
          · have e : i = 133 := by omega
            subst i
            exact ok133
          · have e : i = 134 := by omega
            subst i
            exact ok134
      · by_cases h135_138 : i < 136
        · have e : i = 135 := by omega
          subst i
          exact ok135
        · by_cases h136_138 : i < 137
          · have e : i = 136 := by omega
            subst i
            exact ok136
          · have e : i = 137 := by omega
            subst i
            exact ok137
    · by_cases h138_144 : i < 141
      · by_cases h138_141 : i < 139
        · have e : i = 138 := by omega
          subst i
          exact ok138
        · by_cases h139_141 : i < 140
          · have e : i = 139 := by omega
            subst i
            exact ok139
          · have e : i = 140 := by omega
            subst i
            exact ok140
      · by_cases h141_144 : i < 142
        · have e : i = 141 := by omega
          subst i
          exact ok141
        · by_cases h142_144 : i < 143
          · have e : i = 142 := by omega
            subst i
            exact ok142
          · have e : i = 143 := by omega
            subst i
            exact ok143
end HaarMetaS014Data
