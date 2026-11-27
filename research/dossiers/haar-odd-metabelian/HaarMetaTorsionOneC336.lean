import HaarMetaTorsionOneData
namespace HaarMetaTorsionOneData
open HaarMetaTorsionOneDAG HaarMetaTorsionOneVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok336 : valid D 336 := by decide +kernel
private theorem ok337 : valid D 337 := by decide +kernel
private theorem ok338 : valid D 338 := by decide +kernel
private theorem ok339 : valid D 339 := by decide +kernel
private theorem ok340 : valid D 340 := by decide +kernel
private theorem ok341 : valid D 341 := by decide +kernel
private theorem ok342 : valid D 342 := by decide +kernel
private theorem ok343 : valid D 343 := by decide +kernel
private theorem ok344 : valid D 344 := by decide +kernel
private theorem ok345 : valid D 345 := by decide +kernel
private theorem ok346 : valid D 346 := by decide +kernel
private theorem ok347 : valid D 347 := by decide +kernel
private theorem ok348 : valid D 348 := by decide +kernel
private theorem ok349 : valid D 349 := by decide +kernel
private theorem ok350 : valid D 350 := by decide +kernel
private theorem ok351 : valid D 351 := by decide +kernel
private theorem ok352 : valid D 352 := by decide +kernel
private theorem ok353 : valid D 353 := by decide +kernel
private theorem ok354 : valid D 354 := by decide +kernel
private theorem ok355 : valid D 355 := by decide +kernel
private theorem ok356 : valid D 356 := by decide +kernel
private theorem ok357 : valid D 357 := by decide +kernel
private theorem ok358 : valid D 358 := by decide +kernel
private theorem ok359 : valid D 359 := by decide +kernel
theorem C336valid (i : Nat) (_lo : 336 ≤ i) (_hi : i < 360) : valid D i := by
  by_cases h336_360 : i < 348
  · by_cases h336_348 : i < 342
    · by_cases h336_342 : i < 339
      · by_cases h336_339 : i < 337
        · have e : i = 336 := by omega
          subst i
          exact ok336
        · by_cases h337_339 : i < 338
          · have e : i = 337 := by omega
            subst i
            exact ok337
          · have e : i = 338 := by omega
            subst i
            exact ok338
      · by_cases h339_342 : i < 340
        · have e : i = 339 := by omega
          subst i
          exact ok339
        · by_cases h340_342 : i < 341
          · have e : i = 340 := by omega
            subst i
            exact ok340
          · have e : i = 341 := by omega
            subst i
            exact ok341
    · by_cases h342_348 : i < 345
      · by_cases h342_345 : i < 343
        · have e : i = 342 := by omega
          subst i
          exact ok342
        · by_cases h343_345 : i < 344
          · have e : i = 343 := by omega
            subst i
            exact ok343
          · have e : i = 344 := by omega
            subst i
            exact ok344
      · by_cases h345_348 : i < 346
        · have e : i = 345 := by omega
          subst i
          exact ok345
        · by_cases h346_348 : i < 347
          · have e : i = 346 := by omega
            subst i
            exact ok346
          · have e : i = 347 := by omega
            subst i
            exact ok347
  · by_cases h348_360 : i < 354
    · by_cases h348_354 : i < 351
      · by_cases h348_351 : i < 349
        · have e : i = 348 := by omega
          subst i
          exact ok348
        · by_cases h349_351 : i < 350
          · have e : i = 349 := by omega
            subst i
            exact ok349
          · have e : i = 350 := by omega
            subst i
            exact ok350
      · by_cases h351_354 : i < 352
        · have e : i = 351 := by omega
          subst i
          exact ok351
        · by_cases h352_354 : i < 353
          · have e : i = 352 := by omega
            subst i
            exact ok352
          · have e : i = 353 := by omega
            subst i
            exact ok353
    · by_cases h354_360 : i < 357
      · by_cases h354_357 : i < 355
        · have e : i = 354 := by omega
          subst i
          exact ok354
        · by_cases h355_357 : i < 356
          · have e : i = 355 := by omega
            subst i
            exact ok355
          · have e : i = 356 := by omega
            subst i
            exact ok356
      · by_cases h357_360 : i < 358
        · have e : i = 357 := by omega
          subst i
          exact ok357
        · by_cases h358_360 : i < 359
          · have e : i = 358 := by omega
            subst i
            exact ok358
          · have e : i = 359 := by omega
            subst i
            exact ok359
end HaarMetaTorsionOneData
