import HaarMetaTorusData
namespace HaarMetaTorusData
open HaarMetaTorusDAG HaarMetaTorusVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok224 : valid D 224 := by decide +kernel
private theorem ok225 : valid D 225 := by decide +kernel
private theorem ok226 : valid D 226 := by decide +kernel
private theorem ok227 : valid D 227 := by decide +kernel
private theorem ok228 : valid D 228 := by decide +kernel
private theorem ok229 : valid D 229 := by decide +kernel
private theorem ok230 : valid D 230 := by decide +kernel
private theorem ok231 : valid D 231 := by decide +kernel
private theorem ok232 : valid D 232 := by decide +kernel
private theorem ok233 : valid D 233 := by decide +kernel
private theorem ok234 : valid D 234 := by decide +kernel
private theorem ok235 : valid D 235 := by decide +kernel
private theorem ok236 : valid D 236 := by decide +kernel
private theorem ok237 : valid D 237 := by decide +kernel
private theorem ok238 : valid D 238 := by decide +kernel
private theorem ok239 : valid D 239 := by decide +kernel
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
theorem C224valid (i : Nat) (_lo : 224 ≤ i) (_hi : i < 256) : valid D i := by
  by_cases h224_256 : i < 240
  · by_cases h224_240 : i < 232
    · by_cases h224_232 : i < 228
      · by_cases h224_228 : i < 226
        · by_cases h224_226 : i < 225
          · have e : i = 224 := by omega
            subst i
            exact ok224
          · have e : i = 225 := by omega
            subst i
            exact ok225
        · by_cases h226_228 : i < 227
          · have e : i = 226 := by omega
            subst i
            exact ok226
          · have e : i = 227 := by omega
            subst i
            exact ok227
      · by_cases h228_232 : i < 230
        · by_cases h228_230 : i < 229
          · have e : i = 228 := by omega
            subst i
            exact ok228
          · have e : i = 229 := by omega
            subst i
            exact ok229
        · by_cases h230_232 : i < 231
          · have e : i = 230 := by omega
            subst i
            exact ok230
          · have e : i = 231 := by omega
            subst i
            exact ok231
    · by_cases h232_240 : i < 236
      · by_cases h232_236 : i < 234
        · by_cases h232_234 : i < 233
          · have e : i = 232 := by omega
            subst i
            exact ok232
          · have e : i = 233 := by omega
            subst i
            exact ok233
        · by_cases h234_236 : i < 235
          · have e : i = 234 := by omega
            subst i
            exact ok234
          · have e : i = 235 := by omega
            subst i
            exact ok235
      · by_cases h236_240 : i < 238
        · by_cases h236_238 : i < 237
          · have e : i = 236 := by omega
            subst i
            exact ok236
          · have e : i = 237 := by omega
            subst i
            exact ok237
        · by_cases h238_240 : i < 239
          · have e : i = 238 := by omega
            subst i
            exact ok238
          · have e : i = 239 := by omega
            subst i
            exact ok239
  · by_cases h240_256 : i < 248
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
end HaarMetaTorusData
