import HaarMetaTorsionOneData
namespace HaarMetaTorsionOneData
open HaarMetaTorsionOneDAG HaarMetaTorsionOneVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok264 : valid D 264 := by decide +kernel
private theorem ok265 : valid D 265 := by decide +kernel
private theorem ok266 : valid D 266 := by decide +kernel
private theorem ok267 : valid D 267 := by decide +kernel
private theorem ok268 : valid D 268 := by decide +kernel
private theorem ok269 : valid D 269 := by decide +kernel
private theorem ok270 : valid D 270 := by decide +kernel
private theorem ok271 : valid D 271 := by decide +kernel
private theorem ok272 : valid D 272 := by decide +kernel
private theorem ok273 : valid D 273 := by decide +kernel
private theorem ok274 : valid D 274 := by decide +kernel
private theorem ok275 : valid D 275 := by decide +kernel
private theorem ok276 : valid D 276 := by decide +kernel
private theorem ok277 : valid D 277 := by decide +kernel
private theorem ok278 : valid D 278 := by decide +kernel
private theorem ok279 : valid D 279 := by decide +kernel
private theorem ok280 : valid D 280 := by decide +kernel
private theorem ok281 : valid D 281 := by decide +kernel
private theorem ok282 : valid D 282 := by decide +kernel
private theorem ok283 : valid D 283 := by decide +kernel
private theorem ok284 : valid D 284 := by decide +kernel
private theorem ok285 : valid D 285 := by decide +kernel
private theorem ok286 : valid D 286 := by decide +kernel
private theorem ok287 : valid D 287 := by decide +kernel
theorem C264valid (i : Nat) (_lo : 264 ≤ i) (_hi : i < 288) : valid D i := by
  by_cases h264_288 : i < 276
  · by_cases h264_276 : i < 270
    · by_cases h264_270 : i < 267
      · by_cases h264_267 : i < 265
        · have e : i = 264 := by omega
          subst i
          exact ok264
        · by_cases h265_267 : i < 266
          · have e : i = 265 := by omega
            subst i
            exact ok265
          · have e : i = 266 := by omega
            subst i
            exact ok266
      · by_cases h267_270 : i < 268
        · have e : i = 267 := by omega
          subst i
          exact ok267
        · by_cases h268_270 : i < 269
          · have e : i = 268 := by omega
            subst i
            exact ok268
          · have e : i = 269 := by omega
            subst i
            exact ok269
    · by_cases h270_276 : i < 273
      · by_cases h270_273 : i < 271
        · have e : i = 270 := by omega
          subst i
          exact ok270
        · by_cases h271_273 : i < 272
          · have e : i = 271 := by omega
            subst i
            exact ok271
          · have e : i = 272 := by omega
            subst i
            exact ok272
      · by_cases h273_276 : i < 274
        · have e : i = 273 := by omega
          subst i
          exact ok273
        · by_cases h274_276 : i < 275
          · have e : i = 274 := by omega
            subst i
            exact ok274
          · have e : i = 275 := by omega
            subst i
            exact ok275
  · by_cases h276_288 : i < 282
    · by_cases h276_282 : i < 279
      · by_cases h276_279 : i < 277
        · have e : i = 276 := by omega
          subst i
          exact ok276
        · by_cases h277_279 : i < 278
          · have e : i = 277 := by omega
            subst i
            exact ok277
          · have e : i = 278 := by omega
            subst i
            exact ok278
      · by_cases h279_282 : i < 280
        · have e : i = 279 := by omega
          subst i
          exact ok279
        · by_cases h280_282 : i < 281
          · have e : i = 280 := by omega
            subst i
            exact ok280
          · have e : i = 281 := by omega
            subst i
            exact ok281
    · by_cases h282_288 : i < 285
      · by_cases h282_285 : i < 283
        · have e : i = 282 := by omega
          subst i
          exact ok282
        · by_cases h283_285 : i < 284
          · have e : i = 283 := by omega
            subst i
            exact ok283
          · have e : i = 284 := by omega
            subst i
            exact ok284
      · by_cases h285_288 : i < 286
        · have e : i = 285 := by omega
          subst i
          exact ok285
        · by_cases h286_288 : i < 287
          · have e : i = 286 := by omega
            subst i
            exact ok286
          · have e : i = 287 := by omega
            subst i
            exact ok287
end HaarMetaTorsionOneData
