import HaarStripData
namespace HaarStripData
open HaarStripDAG HaarStripVoltage
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
theorem C288valid (i : Nat) (_lo : 288 ≤ i) (_hi : i < 312) : valid D i := by
  by_cases h288_312 : i < 300
  · by_cases h288_300 : i < 294
    · by_cases h288_294 : i < 291
      · by_cases h288_291 : i < 289
        · have e : i = 288 := by omega
          subst i
          exact ok288
        · by_cases h289_291 : i < 290
          · have e : i = 289 := by omega
            subst i
            exact ok289
          · have e : i = 290 := by omega
            subst i
            exact ok290
      · by_cases h291_294 : i < 292
        · have e : i = 291 := by omega
          subst i
          exact ok291
        · by_cases h292_294 : i < 293
          · have e : i = 292 := by omega
            subst i
            exact ok292
          · have e : i = 293 := by omega
            subst i
            exact ok293
    · by_cases h294_300 : i < 297
      · by_cases h294_297 : i < 295
        · have e : i = 294 := by omega
          subst i
          exact ok294
        · by_cases h295_297 : i < 296
          · have e : i = 295 := by omega
            subst i
            exact ok295
          · have e : i = 296 := by omega
            subst i
            exact ok296
      · by_cases h297_300 : i < 298
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
  · by_cases h300_312 : i < 306
    · by_cases h300_306 : i < 303
      · by_cases h300_303 : i < 301
        · have e : i = 300 := by omega
          subst i
          exact ok300
        · by_cases h301_303 : i < 302
          · have e : i = 301 := by omega
            subst i
            exact ok301
          · have e : i = 302 := by omega
            subst i
            exact ok302
      · by_cases h303_306 : i < 304
        · have e : i = 303 := by omega
          subst i
          exact ok303
        · by_cases h304_306 : i < 305
          · have e : i = 304 := by omega
            subst i
            exact ok304
          · have e : i = 305 := by omega
            subst i
            exact ok305
    · by_cases h306_312 : i < 309
      · by_cases h306_309 : i < 307
        · have e : i = 306 := by omega
          subst i
          exact ok306
        · by_cases h307_309 : i < 308
          · have e : i = 307 := by omega
            subst i
            exact ok307
          · have e : i = 308 := by omega
            subst i
            exact ok308
      · by_cases h309_312 : i < 310
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
end HaarStripData
