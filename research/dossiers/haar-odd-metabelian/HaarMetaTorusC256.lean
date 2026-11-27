import HaarMetaTorusData
namespace HaarMetaTorusData
open HaarMetaTorusDAG HaarMetaTorusVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok256 : valid D 256 := by decide +kernel
private theorem ok257 : valid D 257 := by decide +kernel
private theorem ok258 : valid D 258 := by decide +kernel
private theorem ok259 : valid D 259 := by decide +kernel
private theorem ok260 : valid D 260 := by decide +kernel
private theorem ok261 : valid D 261 := by decide +kernel
private theorem ok262 : valid D 262 := by decide +kernel
private theorem ok263 : valid D 263 := by decide +kernel
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
theorem C256valid (i : Nat) (_lo : 256 ≤ i) (_hi : i < 288) : valid D i := by
  by_cases h256_288 : i < 272
  · by_cases h256_272 : i < 264
    · by_cases h256_264 : i < 260
      · by_cases h256_260 : i < 258
        · by_cases h256_258 : i < 257
          · have e : i = 256 := by omega
            subst i
            exact ok256
          · have e : i = 257 := by omega
            subst i
            exact ok257
        · by_cases h258_260 : i < 259
          · have e : i = 258 := by omega
            subst i
            exact ok258
          · have e : i = 259 := by omega
            subst i
            exact ok259
      · by_cases h260_264 : i < 262
        · by_cases h260_262 : i < 261
          · have e : i = 260 := by omega
            subst i
            exact ok260
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
    · by_cases h264_272 : i < 268
      · by_cases h264_268 : i < 266
        · by_cases h264_266 : i < 265
          · have e : i = 264 := by omega
            subst i
            exact ok264
          · have e : i = 265 := by omega
            subst i
            exact ok265
        · by_cases h266_268 : i < 267
          · have e : i = 266 := by omega
            subst i
            exact ok266
          · have e : i = 267 := by omega
            subst i
            exact ok267
      · by_cases h268_272 : i < 270
        · by_cases h268_270 : i < 269
          · have e : i = 268 := by omega
            subst i
            exact ok268
          · have e : i = 269 := by omega
            subst i
            exact ok269
        · by_cases h270_272 : i < 271
          · have e : i = 270 := by omega
            subst i
            exact ok270
          · have e : i = 271 := by omega
            subst i
            exact ok271
  · by_cases h272_288 : i < 280
    · by_cases h272_280 : i < 276
      · by_cases h272_276 : i < 274
        · by_cases h272_274 : i < 273
          · have e : i = 272 := by omega
            subst i
            exact ok272
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
      · by_cases h276_280 : i < 278
        · by_cases h276_278 : i < 277
          · have e : i = 276 := by omega
            subst i
            exact ok276
          · have e : i = 277 := by omega
            subst i
            exact ok277
        · by_cases h278_280 : i < 279
          · have e : i = 278 := by omega
            subst i
            exact ok278
          · have e : i = 279 := by omega
            subst i
            exact ok279
    · by_cases h280_288 : i < 284
      · by_cases h280_284 : i < 282
        · by_cases h280_282 : i < 281
          · have e : i = 280 := by omega
            subst i
            exact ok280
          · have e : i = 281 := by omega
            subst i
            exact ok281
        · by_cases h282_284 : i < 283
          · have e : i = 282 := by omega
            subst i
            exact ok282
          · have e : i = 283 := by omega
            subst i
            exact ok283
      · by_cases h284_288 : i < 286
        · by_cases h284_286 : i < 285
          · have e : i = 284 := by omega
            subst i
            exact ok284
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
end HaarMetaTorusData
