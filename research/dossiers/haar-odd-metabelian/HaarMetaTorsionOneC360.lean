import HaarMetaTorsionOneData
namespace HaarMetaTorsionOneData
open HaarMetaTorsionOneDAG HaarMetaTorsionOneVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok360 : valid D 360 := by decide +kernel
private theorem ok361 : valid D 361 := by decide +kernel
private theorem ok362 : valid D 362 := by decide +kernel
private theorem ok363 : valid D 363 := by decide +kernel
private theorem ok364 : valid D 364 := by decide +kernel
private theorem ok365 : valid D 365 := by decide +kernel
private theorem ok366 : valid D 366 := by decide +kernel
private theorem ok367 : valid D 367 := by decide +kernel
private theorem ok368 : valid D 368 := by decide +kernel
private theorem ok369 : valid D 369 := by decide +kernel
private theorem ok370 : valid D 370 := by decide +kernel
private theorem ok371 : valid D 371 := by decide +kernel
private theorem ok372 : valid D 372 := by decide +kernel
private theorem ok373 : valid D 373 := by decide +kernel
private theorem ok374 : valid D 374 := by decide +kernel
private theorem ok375 : valid D 375 := by decide +kernel
private theorem ok376 : valid D 376 := by decide +kernel
private theorem ok377 : valid D 377 := by decide +kernel
private theorem ok378 : valid D 378 := by decide +kernel
private theorem ok379 : valid D 379 := by decide +kernel
private theorem ok380 : valid D 380 := by decide +kernel
private theorem ok381 : valid D 381 := by decide +kernel
private theorem ok382 : valid D 382 := by decide +kernel
private theorem ok383 : valid D 383 := by decide +kernel
theorem C360valid (i : Nat) (_lo : 360 ≤ i) (_hi : i < 384) : valid D i := by
  by_cases h360_384 : i < 372
  · by_cases h360_372 : i < 366
    · by_cases h360_366 : i < 363
      · by_cases h360_363 : i < 361
        · have e : i = 360 := by omega
          subst i
          exact ok360
        · by_cases h361_363 : i < 362
          · have e : i = 361 := by omega
            subst i
            exact ok361
          · have e : i = 362 := by omega
            subst i
            exact ok362
      · by_cases h363_366 : i < 364
        · have e : i = 363 := by omega
          subst i
          exact ok363
        · by_cases h364_366 : i < 365
          · have e : i = 364 := by omega
            subst i
            exact ok364
          · have e : i = 365 := by omega
            subst i
            exact ok365
    · by_cases h366_372 : i < 369
      · by_cases h366_369 : i < 367
        · have e : i = 366 := by omega
          subst i
          exact ok366
        · by_cases h367_369 : i < 368
          · have e : i = 367 := by omega
            subst i
            exact ok367
          · have e : i = 368 := by omega
            subst i
            exact ok368
      · by_cases h369_372 : i < 370
        · have e : i = 369 := by omega
          subst i
          exact ok369
        · by_cases h370_372 : i < 371
          · have e : i = 370 := by omega
            subst i
            exact ok370
          · have e : i = 371 := by omega
            subst i
            exact ok371
  · by_cases h372_384 : i < 378
    · by_cases h372_378 : i < 375
      · by_cases h372_375 : i < 373
        · have e : i = 372 := by omega
          subst i
          exact ok372
        · by_cases h373_375 : i < 374
          · have e : i = 373 := by omega
            subst i
            exact ok373
          · have e : i = 374 := by omega
            subst i
            exact ok374
      · by_cases h375_378 : i < 376
        · have e : i = 375 := by omega
          subst i
          exact ok375
        · by_cases h376_378 : i < 377
          · have e : i = 376 := by omega
            subst i
            exact ok376
          · have e : i = 377 := by omega
            subst i
            exact ok377
    · by_cases h378_384 : i < 381
      · by_cases h378_381 : i < 379
        · have e : i = 378 := by omega
          subst i
          exact ok378
        · by_cases h379_381 : i < 380
          · have e : i = 379 := by omega
            subst i
            exact ok379
          · have e : i = 380 := by omega
            subst i
            exact ok380
      · by_cases h381_384 : i < 382
        · have e : i = 381 := by omega
          subst i
          exact ok381
        · by_cases h382_384 : i < 383
          · have e : i = 382 := by omega
            subst i
            exact ok382
          · have e : i = 383 := by omega
            subst i
            exact ok383
end HaarMetaTorsionOneData
