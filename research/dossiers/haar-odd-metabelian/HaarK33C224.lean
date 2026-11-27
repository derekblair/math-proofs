import HaarK33Data
namespace HaarK33Data
open HaarK33DAG HaarK33Voltage
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
theorem C224valid (i : Nat) (_lo : 224 ≤ i) (_hi : i < 240) : valid D i := by
  by_cases h224_240 : i < 232
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
end HaarK33Data
