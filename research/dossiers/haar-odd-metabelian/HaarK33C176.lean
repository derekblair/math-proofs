import HaarK33Data
namespace HaarK33Data
open HaarK33DAG HaarK33Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
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
theorem C176valid (i : Nat) (_lo : 176 ≤ i) (_hi : i < 192) : valid D i := by
  by_cases h176_192 : i < 184
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
end HaarK33Data
