import HaarStripData
namespace HaarStripData
open HaarStripDAG HaarStripVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok216 : valid D 216 := by decide +kernel
private theorem ok217 : valid D 217 := by decide +kernel
private theorem ok218 : valid D 218 := by decide +kernel
private theorem ok219 : valid D 219 := by decide +kernel
private theorem ok220 : valid D 220 := by decide +kernel
private theorem ok221 : valid D 221 := by decide +kernel
private theorem ok222 : valid D 222 := by decide +kernel
private theorem ok223 : valid D 223 := by decide +kernel
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
theorem C216valid (i : Nat) (_lo : 216 ≤ i) (_hi : i < 240) : valid D i := by
  by_cases h216_240 : i < 228
  · by_cases h216_228 : i < 222
    · by_cases h216_222 : i < 219
      · by_cases h216_219 : i < 217
        · have e : i = 216 := by omega
          subst i
          exact ok216
        · by_cases h217_219 : i < 218
          · have e : i = 217 := by omega
            subst i
            exact ok217
          · have e : i = 218 := by omega
            subst i
            exact ok218
      · by_cases h219_222 : i < 220
        · have e : i = 219 := by omega
          subst i
          exact ok219
        · by_cases h220_222 : i < 221
          · have e : i = 220 := by omega
            subst i
            exact ok220
          · have e : i = 221 := by omega
            subst i
            exact ok221
    · by_cases h222_228 : i < 225
      · by_cases h222_225 : i < 223
        · have e : i = 222 := by omega
          subst i
          exact ok222
        · by_cases h223_225 : i < 224
          · have e : i = 223 := by omega
            subst i
            exact ok223
          · have e : i = 224 := by omega
            subst i
            exact ok224
      · by_cases h225_228 : i < 226
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
  · by_cases h228_240 : i < 234
    · by_cases h228_234 : i < 231
      · by_cases h228_231 : i < 229
        · have e : i = 228 := by omega
          subst i
          exact ok228
        · by_cases h229_231 : i < 230
          · have e : i = 229 := by omega
            subst i
            exact ok229
          · have e : i = 230 := by omega
            subst i
            exact ok230
      · by_cases h231_234 : i < 232
        · have e : i = 231 := by omega
          subst i
          exact ok231
        · by_cases h232_234 : i < 233
          · have e : i = 232 := by omega
            subst i
            exact ok232
          · have e : i = 233 := by omega
            subst i
            exact ok233
    · by_cases h234_240 : i < 237
      · by_cases h234_237 : i < 235
        · have e : i = 234 := by omega
          subst i
          exact ok234
        · by_cases h235_237 : i < 236
          · have e : i = 235 := by omega
            subst i
            exact ok235
          · have e : i = 236 := by omega
            subst i
            exact ok236
      · by_cases h237_240 : i < 238
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
end HaarStripData
