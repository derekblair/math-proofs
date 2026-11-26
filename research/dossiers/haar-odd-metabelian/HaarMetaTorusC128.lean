import HaarMetaTorusData
namespace HaarMetaTorusData
open HaarMetaTorusDAG HaarMetaTorusVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
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
private theorem ok144 : valid D 144 := by decide +kernel
private theorem ok145 : valid D 145 := by decide +kernel
private theorem ok146 : valid D 146 := by decide +kernel
private theorem ok147 : valid D 147 := by decide +kernel
private theorem ok148 : valid D 148 := by decide +kernel
private theorem ok149 : valid D 149 := by decide +kernel
private theorem ok150 : valid D 150 := by decide +kernel
private theorem ok151 : valid D 151 := by decide +kernel
private theorem ok152 : valid D 152 := by decide +kernel
private theorem ok153 : valid D 153 := by decide +kernel
private theorem ok154 : valid D 154 := by decide +kernel
private theorem ok155 : valid D 155 := by decide +kernel
private theorem ok156 : valid D 156 := by decide +kernel
private theorem ok157 : valid D 157 := by decide +kernel
private theorem ok158 : valid D 158 := by decide +kernel
private theorem ok159 : valid D 159 := by decide +kernel
theorem C128valid (i : Nat) (_lo : 128 ≤ i) (_hi : i < 160) : valid D i := by
  by_cases h128_160 : i < 144
  · by_cases h128_144 : i < 136
    · by_cases h128_136 : i < 132
      · by_cases h128_132 : i < 130
        · by_cases h128_130 : i < 129
          · have e : i = 128 := by omega
            subst i
            exact ok128
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
      · by_cases h132_136 : i < 134
        · by_cases h132_134 : i < 133
          · have e : i = 132 := by omega
            subst i
            exact ok132
          · have e : i = 133 := by omega
            subst i
            exact ok133
        · by_cases h134_136 : i < 135
          · have e : i = 134 := by omega
            subst i
            exact ok134
          · have e : i = 135 := by omega
            subst i
            exact ok135
    · by_cases h136_144 : i < 140
      · by_cases h136_140 : i < 138
        · by_cases h136_138 : i < 137
          · have e : i = 136 := by omega
            subst i
            exact ok136
          · have e : i = 137 := by omega
            subst i
            exact ok137
        · by_cases h138_140 : i < 139
          · have e : i = 138 := by omega
            subst i
            exact ok138
          · have e : i = 139 := by omega
            subst i
            exact ok139
      · by_cases h140_144 : i < 142
        · by_cases h140_142 : i < 141
          · have e : i = 140 := by omega
            subst i
            exact ok140
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
  · by_cases h144_160 : i < 152
    · by_cases h144_152 : i < 148
      · by_cases h144_148 : i < 146
        · by_cases h144_146 : i < 145
          · have e : i = 144 := by omega
            subst i
            exact ok144
          · have e : i = 145 := by omega
            subst i
            exact ok145
        · by_cases h146_148 : i < 147
          · have e : i = 146 := by omega
            subst i
            exact ok146
          · have e : i = 147 := by omega
            subst i
            exact ok147
      · by_cases h148_152 : i < 150
        · by_cases h148_150 : i < 149
          · have e : i = 148 := by omega
            subst i
            exact ok148
          · have e : i = 149 := by omega
            subst i
            exact ok149
        · by_cases h150_152 : i < 151
          · have e : i = 150 := by omega
            subst i
            exact ok150
          · have e : i = 151 := by omega
            subst i
            exact ok151
    · by_cases h152_160 : i < 156
      · by_cases h152_156 : i < 154
        · by_cases h152_154 : i < 153
          · have e : i = 152 := by omega
            subst i
            exact ok152
          · have e : i = 153 := by omega
            subst i
            exact ok153
        · by_cases h154_156 : i < 155
          · have e : i = 154 := by omega
            subst i
            exact ok154
          · have e : i = 155 := by omega
            subst i
            exact ok155
      · by_cases h156_160 : i < 158
        · by_cases h156_158 : i < 157
          · have e : i = 156 := by omega
            subst i
            exact ok156
          · have e : i = 157 := by omega
            subst i
            exact ok157
        · by_cases h158_160 : i < 159
          · have e : i = 158 := by omega
            subst i
            exact ok158
          · have e : i = 159 := by omega
            subst i
            exact ok159
end HaarMetaTorusData
