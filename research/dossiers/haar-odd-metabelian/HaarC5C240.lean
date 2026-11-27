import HaarC5Data
namespace HaarC5Data
open HaarC5DAG HaarC5Voltage
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
private theorem ok256 : valid D 256 := by decide +kernel
private theorem ok257 : valid D 257 := by decide +kernel
private theorem ok258 : valid D 258 := by decide +kernel
private theorem ok259 : valid D 259 := by decide +kernel
private theorem ok260 : valid D 260 := by decide +kernel
private theorem ok261 : valid D 261 := by decide +kernel
private theorem ok262 : valid D 262 := by decide +kernel
private theorem ok263 : valid D 263 := by decide +kernel
theorem C240valid (i : Nat) (_lo : 240 ≤ i) (_hi : i < 264) : valid D i := by
  by_cases h240_264 : i < 252
  · by_cases h240_252 : i < 246
    · by_cases h240_246 : i < 243
      · by_cases h240_243 : i < 241
        · have e : i = 240 := by omega
          subst i
          exact ok240
        · by_cases h241_243 : i < 242
          · have e : i = 241 := by omega
            subst i
            exact ok241
          · have e : i = 242 := by omega
            subst i
            exact ok242
      · by_cases h243_246 : i < 244
        · have e : i = 243 := by omega
          subst i
          exact ok243
        · by_cases h244_246 : i < 245
          · have e : i = 244 := by omega
            subst i
            exact ok244
          · have e : i = 245 := by omega
            subst i
            exact ok245
    · by_cases h246_252 : i < 249
      · by_cases h246_249 : i < 247
        · have e : i = 246 := by omega
          subst i
          exact ok246
        · by_cases h247_249 : i < 248
          · have e : i = 247 := by omega
            subst i
            exact ok247
          · have e : i = 248 := by omega
            subst i
            exact ok248
      · by_cases h249_252 : i < 250
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
  · by_cases h252_264 : i < 258
    · by_cases h252_258 : i < 255
      · by_cases h252_255 : i < 253
        · have e : i = 252 := by omega
          subst i
          exact ok252
        · by_cases h253_255 : i < 254
          · have e : i = 253 := by omega
            subst i
            exact ok253
          · have e : i = 254 := by omega
            subst i
            exact ok254
      · by_cases h255_258 : i < 256
        · have e : i = 255 := by omega
          subst i
          exact ok255
        · by_cases h256_258 : i < 257
          · have e : i = 256 := by omega
            subst i
            exact ok256
          · have e : i = 257 := by omega
            subst i
            exact ok257
    · by_cases h258_264 : i < 261
      · by_cases h258_261 : i < 259
        · have e : i = 258 := by omega
          subst i
          exact ok258
        · by_cases h259_261 : i < 260
          · have e : i = 259 := by omega
            subst i
            exact ok259
          · have e : i = 260 := by omega
            subst i
            exact ok260
      · by_cases h261_264 : i < 262
        · have e : i = 261 := by omega
          subst i
          exact ok261
        · by_cases h262_264 : i < 263
          · have e : i = 262 := by omega
            subst i
            exact ok262
          · have e : i = 263 := by omega
            subst i
            exact ok263
end HaarC5Data
