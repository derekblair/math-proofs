import HaarMetaNineData
namespace HaarMetaNineData
open HaarMetaNineDAG HaarMetaNineVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok288 : valid D 288 := by decide +kernel
private theorem ok289 : valid D 289 := by decide +kernel
private theorem ok290 : valid D 290 := by decide +kernel
private theorem ok291 : valid D 291 := by decide +kernel
private theorem ok292 : valid D 292 := by decide +kernel
private theorem ok293 : valid D 293 := by decide +kernel
private theorem ok294 : valid D 294 := by decide +kernel
private theorem ok295 : valid D 295 := by decide +kernel
private theorem ok296 : valid D 296 := by decide +kernel
private theorem ok297 : valid D 297 := by decide +kernel
private theorem ok298 : valid D 298 := by decide +kernel
private theorem ok299 : valid D 299 := by decide +kernel
private theorem ok300 : valid D 300 := by decide +kernel
private theorem ok301 : valid D 301 := by decide +kernel
private theorem ok302 : valid D 302 := by decide +kernel
private theorem ok303 : valid D 303 := by decide +kernel
private theorem ok304 : valid D 304 := by decide +kernel
private theorem ok305 : valid D 305 := by decide +kernel
private theorem ok306 : valid D 306 := by decide +kernel
private theorem ok307 : valid D 307 := by decide +kernel
private theorem ok308 : valid D 308 := by decide +kernel
private theorem ok309 : valid D 309 := by decide +kernel
private theorem ok310 : valid D 310 := by decide +kernel
private theorem ok311 : valid D 311 := by decide +kernel
private theorem ok312 : valid D 312 := by decide +kernel
private theorem ok313 : valid D 313 := by decide +kernel
private theorem ok314 : valid D 314 := by decide +kernel
private theorem ok315 : valid D 315 := by decide +kernel
private theorem ok316 : valid D 316 := by decide +kernel
private theorem ok317 : valid D 317 := by decide +kernel
private theorem ok318 : valid D 318 := by decide +kernel
private theorem ok319 : valid D 319 := by decide +kernel
theorem C288valid (i : Nat) (_lo : 288 ≤ i) (_hi : i < 320) : valid D i := by
  by_cases h288_320 : i < 304
  · by_cases h288_304 : i < 296
    · by_cases h288_296 : i < 292
      · by_cases h288_292 : i < 290
        · by_cases h288_290 : i < 289
          · have e : i = 288 := by omega
            subst i
            exact ok288
          · have e : i = 289 := by omega
            subst i
            exact ok289
        · by_cases h290_292 : i < 291
          · have e : i = 290 := by omega
            subst i
            exact ok290
          · have e : i = 291 := by omega
            subst i
            exact ok291
      · by_cases h292_296 : i < 294
        · by_cases h292_294 : i < 293
          · have e : i = 292 := by omega
            subst i
            exact ok292
          · have e : i = 293 := by omega
            subst i
            exact ok293
        · by_cases h294_296 : i < 295
          · have e : i = 294 := by omega
            subst i
            exact ok294
          · have e : i = 295 := by omega
            subst i
            exact ok295
    · by_cases h296_304 : i < 300
      · by_cases h296_300 : i < 298
        · by_cases h296_298 : i < 297
          · have e : i = 296 := by omega
            subst i
            exact ok296
          · have e : i = 297 := by omega
            subst i
            exact ok297
        · by_cases h298_300 : i < 299
          · have e : i = 298 := by omega
            subst i
            exact ok298
          · have e : i = 299 := by omega
            subst i
            exact ok299
      · by_cases h300_304 : i < 302
        · by_cases h300_302 : i < 301
          · have e : i = 300 := by omega
            subst i
            exact ok300
          · have e : i = 301 := by omega
            subst i
            exact ok301
        · by_cases h302_304 : i < 303
          · have e : i = 302 := by omega
            subst i
            exact ok302
          · have e : i = 303 := by omega
            subst i
            exact ok303
  · by_cases h304_320 : i < 312
    · by_cases h304_312 : i < 308
      · by_cases h304_308 : i < 306
        · by_cases h304_306 : i < 305
          · have e : i = 304 := by omega
            subst i
            exact ok304
          · have e : i = 305 := by omega
            subst i
            exact ok305
        · by_cases h306_308 : i < 307
          · have e : i = 306 := by omega
            subst i
            exact ok306
          · have e : i = 307 := by omega
            subst i
            exact ok307
      · by_cases h308_312 : i < 310
        · by_cases h308_310 : i < 309
          · have e : i = 308 := by omega
            subst i
            exact ok308
          · have e : i = 309 := by omega
            subst i
            exact ok309
        · by_cases h310_312 : i < 311
          · have e : i = 310 := by omega
            subst i
            exact ok310
          · have e : i = 311 := by omega
            subst i
            exact ok311
    · by_cases h312_320 : i < 316
      · by_cases h312_316 : i < 314
        · by_cases h312_314 : i < 313
          · have e : i = 312 := by omega
            subst i
            exact ok312
          · have e : i = 313 := by omega
            subst i
            exact ok313
        · by_cases h314_316 : i < 315
          · have e : i = 314 := by omega
            subst i
            exact ok314
          · have e : i = 315 := by omega
            subst i
            exact ok315
      · by_cases h316_320 : i < 318
        · by_cases h316_318 : i < 317
          · have e : i = 316 := by omega
            subst i
            exact ok316
          · have e : i = 317 := by omega
            subst i
            exact ok317
        · by_cases h318_320 : i < 319
          · have e : i = 318 := by omega
            subst i
            exact ok318
          · have e : i = 319 := by omega
            subst i
            exact ok319
end HaarMetaNineData
