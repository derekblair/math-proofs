import HaarK33Data
namespace HaarK33Data
open HaarK33DAG HaarK33Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok240 : valid D 240 := by decide +kernel
private theorem ok241 : valid D 241 := by decide +kernel
private theorem ok242 : valid D 242 := by decide +kernel
private theorem ok243 : valid D 243 := by decide +kernel
private theorem ok244 : valid D 244 := by decide +kernel
private theorem ok245 : valid D 245 := by decide +kernel
private theorem ok246 : valid D 246 := by decide +kernel
private theorem ok247 : valid D 247 := by decide +kernel
private theorem ok248 : valid D 248 := by decide +kernel
private theorem ok249 : valid D 249 := by decide +kernel
private theorem ok250 : valid D 250 := by decide +kernel
private theorem ok251 : valid D 251 := by decide +kernel
private theorem ok252 : valid D 252 := by decide +kernel
private theorem ok253 : valid D 253 := by decide +kernel
private theorem ok254 : valid D 254 := by decide +kernel
private theorem ok255 : valid D 255 := by decide +kernel
theorem C240valid (i : Nat) (_lo : 240 ≤ i) (_hi : i < 256) : valid D i := by
  by_cases h240_256 : i < 248
  · by_cases h240_248 : i < 244
    · by_cases h240_244 : i < 242
      · by_cases h240_242 : i < 241
        · have e : i = 240 := by omega
          subst i
          exact ok240
        · have e : i = 241 := by omega
          subst i
          exact ok241
      · by_cases h242_244 : i < 243
        · have e : i = 242 := by omega
          subst i
          exact ok242
        · have e : i = 243 := by omega
          subst i
          exact ok243
    · by_cases h244_248 : i < 246
      · by_cases h244_246 : i < 245
        · have e : i = 244 := by omega
          subst i
          exact ok244
        · have e : i = 245 := by omega
          subst i
          exact ok245
      · by_cases h246_248 : i < 247
        · have e : i = 246 := by omega
          subst i
          exact ok246
        · have e : i = 247 := by omega
          subst i
          exact ok247
  · by_cases h248_256 : i < 252
    · by_cases h248_252 : i < 250
      · by_cases h248_250 : i < 249
        · have e : i = 248 := by omega
          subst i
          exact ok248
        · have e : i = 249 := by omega
          subst i
          exact ok249
      · by_cases h250_252 : i < 251
        · have e : i = 250 := by omega
          subst i
          exact ok250
        · have e : i = 251 := by omega
          subst i
          exact ok251
    · by_cases h252_256 : i < 254
      · by_cases h252_254 : i < 253
        · have e : i = 252 := by omega
          subst i
          exact ok252
        · have e : i = 253 := by omega
          subst i
          exact ok253
      · by_cases h254_256 : i < 255
        · have e : i = 254 := by omega
          subst i
          exact ok254
        · have e : i = 255 := by omega
          subst i
          exact ok255
end HaarK33Data
