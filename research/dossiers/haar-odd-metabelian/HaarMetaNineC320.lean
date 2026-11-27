import HaarMetaNineData
namespace HaarMetaNineData
open HaarMetaNineDAG HaarMetaNineVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
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
private theorem ok335 : valid D 335 := by decide +kernel
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
theorem C320valid (i : Nat) (_lo : 320 ≤ i) (_hi : i < 352) : valid D i := by
  by_cases h320_352 : i < 336
  · by_cases h320_336 : i < 328
    · by_cases h320_328 : i < 324
      · by_cases h320_324 : i < 322
        · by_cases h320_322 : i < 321
          · have e : i = 320 := by omega
            subst i
            exact ok320
          · have e : i = 321 := by omega
            subst i
            exact ok321
        · by_cases h322_324 : i < 323
          · have e : i = 322 := by omega
            subst i
            exact ok322
          · have e : i = 323 := by omega
            subst i
            exact ok323
      · by_cases h324_328 : i < 326
        · by_cases h324_326 : i < 325
          · have e : i = 324 := by omega
            subst i
            exact ok324
          · have e : i = 325 := by omega
            subst i
            exact ok325
        · by_cases h326_328 : i < 327
          · have e : i = 326 := by omega
            subst i
            exact ok326
          · have e : i = 327 := by omega
            subst i
            exact ok327
    · by_cases h328_336 : i < 332
      · by_cases h328_332 : i < 330
        · by_cases h328_330 : i < 329
          · have e : i = 328 := by omega
            subst i
            exact ok328
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
      · by_cases h332_336 : i < 334
        · by_cases h332_334 : i < 333
          · have e : i = 332 := by omega
            subst i
            exact ok332
          · have e : i = 333 := by omega
            subst i
            exact ok333
        · by_cases h334_336 : i < 335
          · have e : i = 334 := by omega
            subst i
            exact ok334
          · have e : i = 335 := by omega
            subst i
            exact ok335
  · by_cases h336_352 : i < 344
    · by_cases h336_344 : i < 340
      · by_cases h336_340 : i < 338
        · by_cases h336_338 : i < 337
          · have e : i = 336 := by omega
            subst i
            exact ok336
          · have e : i = 337 := by omega
            subst i
            exact ok337
        · by_cases h338_340 : i < 339
          · have e : i = 338 := by omega
            subst i
            exact ok338
          · have e : i = 339 := by omega
            subst i
            exact ok339
      · by_cases h340_344 : i < 342
        · by_cases h340_342 : i < 341
          · have e : i = 340 := by omega
            subst i
            exact ok340
          · have e : i = 341 := by omega
            subst i
            exact ok341
        · by_cases h342_344 : i < 343
          · have e : i = 342 := by omega
            subst i
            exact ok342
          · have e : i = 343 := by omega
            subst i
            exact ok343
    · by_cases h344_352 : i < 348
      · by_cases h344_348 : i < 346
        · by_cases h344_346 : i < 345
          · have e : i = 344 := by omega
            subst i
            exact ok344
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
      · by_cases h348_352 : i < 350
        · by_cases h348_350 : i < 349
          · have e : i = 348 := by omega
            subst i
            exact ok348
          · have e : i = 349 := by omega
            subst i
            exact ok349
        · by_cases h350_352 : i < 351
          · have e : i = 350 := by omega
            subst i
            exact ok350
          · have e : i = 351 := by omega
            subst i
            exact ok351
end HaarMetaNineData
