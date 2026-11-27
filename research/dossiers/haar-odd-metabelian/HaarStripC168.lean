import HaarStripData
namespace HaarStripData
open HaarStripDAG HaarStripVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
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
theorem C168valid (i : Nat) (_lo : 168 ≤ i) (_hi : i < 192) : valid D i := by
  by_cases h168_192 : i < 180
  · by_cases h168_180 : i < 174
    · by_cases h168_174 : i < 171
      · by_cases h168_171 : i < 169
        · have e : i = 168 := by omega
          subst i
          exact ok168
        · by_cases h169_171 : i < 170
          · have e : i = 169 := by omega
            subst i
            exact ok169
          · have e : i = 170 := by omega
            subst i
            exact ok170
      · by_cases h171_174 : i < 172
        · have e : i = 171 := by omega
          subst i
          exact ok171
        · by_cases h172_174 : i < 173
          · have e : i = 172 := by omega
            subst i
            exact ok172
          · have e : i = 173 := by omega
            subst i
            exact ok173
    · by_cases h174_180 : i < 177
      · by_cases h174_177 : i < 175
        · have e : i = 174 := by omega
          subst i
          exact ok174
        · by_cases h175_177 : i < 176
          · have e : i = 175 := by omega
            subst i
            exact ok175
          · have e : i = 176 := by omega
            subst i
            exact ok176
      · by_cases h177_180 : i < 178
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
  · by_cases h180_192 : i < 186
    · by_cases h180_186 : i < 183
      · by_cases h180_183 : i < 181
        · have e : i = 180 := by omega
          subst i
          exact ok180
        · by_cases h181_183 : i < 182
          · have e : i = 181 := by omega
            subst i
            exact ok181
          · have e : i = 182 := by omega
            subst i
            exact ok182
      · by_cases h183_186 : i < 184
        · have e : i = 183 := by omega
          subst i
          exact ok183
        · by_cases h184_186 : i < 185
          · have e : i = 184 := by omega
            subst i
            exact ok184
          · have e : i = 185 := by omega
            subst i
            exact ok185
    · by_cases h186_192 : i < 189
      · by_cases h186_189 : i < 187
        · have e : i = 186 := by omega
          subst i
          exact ok186
        · by_cases h187_189 : i < 188
          · have e : i = 187 := by omega
            subst i
            exact ok187
          · have e : i = 188 := by omega
            subst i
            exact ok188
      · by_cases h189_192 : i < 190
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
end HaarStripData
