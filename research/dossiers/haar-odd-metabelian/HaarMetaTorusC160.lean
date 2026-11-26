import HaarMetaTorusData
namespace HaarMetaTorusData
open HaarMetaTorusDAG HaarMetaTorusVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok160 : valid D 160 := by decide +kernel
private theorem ok161 : valid D 161 := by decide +kernel
private theorem ok162 : valid D 162 := by decide +kernel
private theorem ok163 : valid D 163 := by decide +kernel
private theorem ok164 : valid D 164 := by decide +kernel
private theorem ok165 : valid D 165 := by decide +kernel
private theorem ok166 : valid D 166 := by decide +kernel
private theorem ok167 : valid D 167 := by decide +kernel
private theorem ok168 : valid D 168 := by decide +kernel
private theorem ok169 : valid D 169 := by decide +kernel
private theorem ok170 : valid D 170 := by decide +kernel
private theorem ok171 : valid D 171 := by decide +kernel
private theorem ok172 : valid D 172 := by decide +kernel
private theorem ok173 : valid D 173 := by decide +kernel
private theorem ok174 : valid D 174 := by decide +kernel
private theorem ok175 : valid D 175 := by decide +kernel
private theorem ok176 : valid D 176 := by decide +kernel
private theorem ok177 : valid D 177 := by decide +kernel
private theorem ok178 : valid D 178 := by decide +kernel
private theorem ok179 : valid D 179 := by decide +kernel
private theorem ok180 : valid D 180 := by decide +kernel
private theorem ok181 : valid D 181 := by decide +kernel
private theorem ok182 : valid D 182 := by decide +kernel
private theorem ok183 : valid D 183 := by decide +kernel
private theorem ok184 : valid D 184 := by decide +kernel
private theorem ok185 : valid D 185 := by decide +kernel
private theorem ok186 : valid D 186 := by decide +kernel
private theorem ok187 : valid D 187 := by decide +kernel
private theorem ok188 : valid D 188 := by decide +kernel
private theorem ok189 : valid D 189 := by decide +kernel
private theorem ok190 : valid D 190 := by decide +kernel
private theorem ok191 : valid D 191 := by decide +kernel
theorem C160valid (i : Nat) (_lo : 160 ≤ i) (_hi : i < 192) : valid D i := by
  by_cases h160_192 : i < 176
  · by_cases h160_176 : i < 168
    · by_cases h160_168 : i < 164
      · by_cases h160_164 : i < 162
        · by_cases h160_162 : i < 161
          · have e : i = 160 := by omega
            subst i
            exact ok160
          · have e : i = 161 := by omega
            subst i
            exact ok161
        · by_cases h162_164 : i < 163
          · have e : i = 162 := by omega
            subst i
            exact ok162
          · have e : i = 163 := by omega
            subst i
            exact ok163
      · by_cases h164_168 : i < 166
        · by_cases h164_166 : i < 165
          · have e : i = 164 := by omega
            subst i
            exact ok164
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
    · by_cases h168_176 : i < 172
      · by_cases h168_172 : i < 170
        · by_cases h168_170 : i < 169
          · have e : i = 168 := by omega
            subst i
            exact ok168
          · have e : i = 169 := by omega
            subst i
            exact ok169
        · by_cases h170_172 : i < 171
          · have e : i = 170 := by omega
            subst i
            exact ok170
          · have e : i = 171 := by omega
            subst i
            exact ok171
      · by_cases h172_176 : i < 174
        · by_cases h172_174 : i < 173
          · have e : i = 172 := by omega
            subst i
            exact ok172
          · have e : i = 173 := by omega
            subst i
            exact ok173
        · by_cases h174_176 : i < 175
          · have e : i = 174 := by omega
            subst i
            exact ok174
          · have e : i = 175 := by omega
            subst i
            exact ok175
  · by_cases h176_192 : i < 184
    · by_cases h176_184 : i < 180
      · by_cases h176_180 : i < 178
        · by_cases h176_178 : i < 177
          · have e : i = 176 := by omega
            subst i
            exact ok176
          · have e : i = 177 := by omega
            subst i
            exact ok177
        · by_cases h178_180 : i < 179
          · have e : i = 178 := by omega
            subst i
            exact ok178
          · have e : i = 179 := by omega
            subst i
            exact ok179
      · by_cases h180_184 : i < 182
        · by_cases h180_182 : i < 181
          · have e : i = 180 := by omega
            subst i
            exact ok180
          · have e : i = 181 := by omega
            subst i
            exact ok181
        · by_cases h182_184 : i < 183
          · have e : i = 182 := by omega
            subst i
            exact ok182
          · have e : i = 183 := by omega
            subst i
            exact ok183
    · by_cases h184_192 : i < 188
      · by_cases h184_188 : i < 186
        · by_cases h184_186 : i < 185
          · have e : i = 184 := by omega
            subst i
            exact ok184
          · have e : i = 185 := by omega
            subst i
            exact ok185
        · by_cases h186_188 : i < 187
          · have e : i = 186 := by omega
            subst i
            exact ok186
          · have e : i = 187 := by omega
            subst i
            exact ok187
      · by_cases h188_192 : i < 190
        · by_cases h188_190 : i < 189
          · have e : i = 188 := by omega
            subst i
            exact ok188
          · have e : i = 189 := by omega
            subst i
            exact ok189
        · by_cases h190_192 : i < 191
          · have e : i = 190 := by omega
            subst i
            exact ok190
          · have e : i = 191 := by omega
            subst i
            exact ok191
end HaarMetaTorusData
