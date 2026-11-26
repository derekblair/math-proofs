import HaarStripData
namespace HaarStripData
open HaarStripDAG HaarStripVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
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
private theorem ok160 : valid D 160 := by decide +kernel
private theorem ok161 : valid D 161 := by decide +kernel
private theorem ok162 : valid D 162 := by decide +kernel
private theorem ok163 : valid D 163 := by decide +kernel
private theorem ok164 : valid D 164 := by decide +kernel
private theorem ok165 : valid D 165 := by decide +kernel
private theorem ok166 : valid D 166 := by decide +kernel
private theorem ok167 : valid D 167 := by decide +kernel
theorem C144valid (i : Nat) (_lo : 144 ≤ i) (_hi : i < 168) : valid D i := by
  by_cases h144_168 : i < 156
  · by_cases h144_156 : i < 150
    · by_cases h144_150 : i < 147
      · by_cases h144_147 : i < 145
        · have e : i = 144 := by omega
          subst i
          exact ok144
        · by_cases h145_147 : i < 146
          · have e : i = 145 := by omega
            subst i
            exact ok145
          · have e : i = 146 := by omega
            subst i
            exact ok146
      · by_cases h147_150 : i < 148
        · have e : i = 147 := by omega
          subst i
          exact ok147
        · by_cases h148_150 : i < 149
          · have e : i = 148 := by omega
            subst i
            exact ok148
          · have e : i = 149 := by omega
            subst i
            exact ok149
    · by_cases h150_156 : i < 153
      · by_cases h150_153 : i < 151
        · have e : i = 150 := by omega
          subst i
          exact ok150
        · by_cases h151_153 : i < 152
          · have e : i = 151 := by omega
            subst i
            exact ok151
          · have e : i = 152 := by omega
            subst i
            exact ok152
      · by_cases h153_156 : i < 154
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
  · by_cases h156_168 : i < 162
    · by_cases h156_162 : i < 159
      · by_cases h156_159 : i < 157
        · have e : i = 156 := by omega
          subst i
          exact ok156
        · by_cases h157_159 : i < 158
          · have e : i = 157 := by omega
            subst i
            exact ok157
          · have e : i = 158 := by omega
            subst i
            exact ok158
      · by_cases h159_162 : i < 160
        · have e : i = 159 := by omega
          subst i
          exact ok159
        · by_cases h160_162 : i < 161
          · have e : i = 160 := by omega
            subst i
            exact ok160
          · have e : i = 161 := by omega
            subst i
            exact ok161
    · by_cases h162_168 : i < 165
      · by_cases h162_165 : i < 163
        · have e : i = 162 := by omega
          subst i
          exact ok162
        · by_cases h163_165 : i < 164
          · have e : i = 163 := by omega
            subst i
            exact ok163
          · have e : i = 164 := by omega
            subst i
            exact ok164
      · by_cases h165_168 : i < 166
        · have e : i = 165 := by omega
          subst i
          exact ok165
        · by_cases h166_168 : i < 167
          · have e : i = 166 := by omega
            subst i
            exact ok166
          · have e : i = 167 := by omega
            subst i
            exact ok167
end HaarStripData
