import HaarK33Data
namespace HaarK33Data
open HaarK33DAG HaarK33Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok208 : valid D 208 := by decide +kernel
private theorem ok209 : valid D 209 := by decide +kernel
private theorem ok210 : valid D 210 := by decide +kernel
private theorem ok211 : valid D 211 := by decide +kernel
private theorem ok212 : valid D 212 := by decide +kernel
private theorem ok213 : valid D 213 := by decide +kernel
private theorem ok214 : valid D 214 := by decide +kernel
private theorem ok215 : valid D 215 := by decide +kernel
private theorem ok216 : valid D 216 := by decide +kernel
private theorem ok217 : valid D 217 := by decide +kernel
private theorem ok218 : valid D 218 := by decide +kernel
private theorem ok219 : valid D 219 := by decide +kernel
private theorem ok220 : valid D 220 := by decide +kernel
private theorem ok221 : valid D 221 := by decide +kernel
private theorem ok222 : valid D 222 := by decide +kernel
private theorem ok223 : valid D 223 := by decide +kernel
theorem C208valid (i : Nat) (_lo : 208 ≤ i) (_hi : i < 224) : valid D i := by
  by_cases h208_224 : i < 216
  · by_cases h208_216 : i < 212
    · by_cases h208_212 : i < 210
      · by_cases h208_210 : i < 209
        · have e : i = 208 := by omega
          subst i
          exact ok208
        · have e : i = 209 := by omega
          subst i
          exact ok209
      · by_cases h210_212 : i < 211
        · have e : i = 210 := by omega
          subst i
          exact ok210
        · have e : i = 211 := by omega
          subst i
          exact ok211
    · by_cases h212_216 : i < 214
      · by_cases h212_214 : i < 213
        · have e : i = 212 := by omega
          subst i
          exact ok212
        · have e : i = 213 := by omega
          subst i
          exact ok213
      · by_cases h214_216 : i < 215
        · have e : i = 214 := by omega
          subst i
          exact ok214
        · have e : i = 215 := by omega
          subst i
          exact ok215
  · by_cases h216_224 : i < 220
    · by_cases h216_220 : i < 218
      · by_cases h216_218 : i < 217
        · have e : i = 216 := by omega
          subst i
          exact ok216
        · have e : i = 217 := by omega
          subst i
          exact ok217
      · by_cases h218_220 : i < 219
        · have e : i = 218 := by omega
          subst i
          exact ok218
        · have e : i = 219 := by omega
          subst i
          exact ok219
    · by_cases h220_224 : i < 222
      · by_cases h220_222 : i < 221
        · have e : i = 220 := by omega
          subst i
          exact ok220
        · have e : i = 221 := by omega
          subst i
          exact ok221
      · by_cases h222_224 : i < 223
        · have e : i = 222 := by omega
          subst i
          exact ok222
        · have e : i = 223 := by omega
          subst i
          exact ok223
end HaarK33Data
