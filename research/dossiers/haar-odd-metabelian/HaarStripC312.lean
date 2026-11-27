import HaarStripData
namespace HaarStripData
open HaarStripDAG HaarStripVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok312 : valid D 312 := by decide +kernel
private theorem ok313 : valid D 313 := by decide +kernel
private theorem ok314 : valid D 314 := by decide +kernel
private theorem ok315 : valid D 315 := by decide +kernel
private theorem ok316 : valid D 316 := by decide +kernel
private theorem ok317 : valid D 317 := by decide +kernel
private theorem ok318 : valid D 318 := by decide +kernel
private theorem ok319 : valid D 319 := by decide +kernel
private theorem ok320 : valid D 320 := by decide +kernel
private theorem ok321 : valid D 321 := by decide +kernel
private theorem ok322 : valid D 322 := by decide +kernel
private theorem ok323 : valid D 323 := by decide +kernel
private theorem ok324 : valid D 324 := by decide +kernel
private theorem ok325 : valid D 325 := by decide +kernel
private theorem ok326 : valid D 326 := by decide +kernel
private theorem ok327 : valid D 327 := by decide +kernel
private theorem ok328 : valid D 328 := by decide +kernel
private theorem ok329 : valid D 329 := by decide +kernel
private theorem ok330 : valid D 330 := by decide +kernel
private theorem ok331 : valid D 331 := by decide +kernel
private theorem ok332 : valid D 332 := by decide +kernel
private theorem ok333 : valid D 333 := by decide +kernel
private theorem ok334 : valid D 334 := by decide +kernel
theorem C312valid (i : Nat) (_lo : 312 ≤ i) (_hi : i < 335) : valid D i := by
  by_cases h312_335 : i < 323
  · by_cases h312_323 : i < 317
    · by_cases h312_317 : i < 314
      · by_cases h312_314 : i < 313
        · have e : i = 312 := by omega
          subst i
          exact ok312
        · have e : i = 313 := by omega
          subst i
          exact ok313
      · by_cases h314_317 : i < 315
        · have e : i = 314 := by omega
          subst i
          exact ok314
        · by_cases h315_317 : i < 316
          · have e : i = 315 := by omega
            subst i
            exact ok315
          · have e : i = 316 := by omega
            subst i
            exact ok316
    · by_cases h317_323 : i < 320
      · by_cases h317_320 : i < 318
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
      · by_cases h320_323 : i < 321
        · have e : i = 320 := by omega
          subst i
          exact ok320
        · by_cases h321_323 : i < 322
          · have e : i = 321 := by omega
            subst i
            exact ok321
          · have e : i = 322 := by omega
            subst i
            exact ok322
  · by_cases h323_335 : i < 329
    · by_cases h323_329 : i < 326
      · by_cases h323_326 : i < 324
        · have e : i = 323 := by omega
          subst i
          exact ok323
        · by_cases h324_326 : i < 325
          · have e : i = 324 := by omega
            subst i
            exact ok324
          · have e : i = 325 := by omega
            subst i
            exact ok325
      · by_cases h326_329 : i < 327
        · have e : i = 326 := by omega
          subst i
          exact ok326
        · by_cases h327_329 : i < 328
          · have e : i = 327 := by omega
            subst i
            exact ok327
          · have e : i = 328 := by omega
            subst i
            exact ok328
    · by_cases h329_335 : i < 332
      · by_cases h329_332 : i < 330
        · have e : i = 329 := by omega
          subst i
          exact ok329
        · by_cases h330_332 : i < 331
          · have e : i = 330 := by omega
            subst i
            exact ok330
          · have e : i = 331 := by omega
            subst i
            exact ok331
      · by_cases h332_335 : i < 333
        · have e : i = 332 := by omega
          subst i
          exact ok332
        · by_cases h333_335 : i < 334
          · have e : i = 333 := by omega
            subst i
            exact ok333
          · have e : i = 334 := by omega
            subst i
            exact ok334
end HaarStripData
