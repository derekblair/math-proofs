import HaarMetaNineData
namespace HaarMetaNineData
open HaarMetaNineDAG HaarMetaNineVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok416 : valid D 416 := by decide +kernel
private theorem ok417 : valid D 417 := by decide +kernel
private theorem ok418 : valid D 418 := by decide +kernel
private theorem ok419 : valid D 419 := by decide +kernel
private theorem ok420 : valid D 420 := by decide +kernel
private theorem ok421 : valid D 421 := by decide +kernel
private theorem ok422 : valid D 422 := by decide +kernel
private theorem ok423 : valid D 423 := by decide +kernel
private theorem ok424 : valid D 424 := by decide +kernel
private theorem ok425 : valid D 425 := by decide +kernel
private theorem ok426 : valid D 426 := by decide +kernel
private theorem ok427 : valid D 427 := by decide +kernel
private theorem ok428 : valid D 428 := by decide +kernel
private theorem ok429 : valid D 429 := by decide +kernel
private theorem ok430 : valid D 430 := by decide +kernel
private theorem ok431 : valid D 431 := by decide +kernel
private theorem ok432 : valid D 432 := by decide +kernel
private theorem ok433 : valid D 433 := by decide +kernel
private theorem ok434 : valid D 434 := by decide +kernel
private theorem ok435 : valid D 435 := by decide +kernel
private theorem ok436 : valid D 436 := by decide +kernel
private theorem ok437 : valid D 437 := by decide +kernel
private theorem ok438 : valid D 438 := by decide +kernel
private theorem ok439 : valid D 439 := by decide +kernel
private theorem ok440 : valid D 440 := by decide +kernel
private theorem ok441 : valid D 441 := by decide +kernel
private theorem ok442 : valid D 442 := by decide +kernel
private theorem ok443 : valid D 443 := by decide +kernel
private theorem ok444 : valid D 444 := by decide +kernel
private theorem ok445 : valid D 445 := by decide +kernel
private theorem ok446 : valid D 446 := by decide +kernel
private theorem ok447 : valid D 447 := by decide +kernel
theorem C416valid (i : Nat) (_lo : 416 ≤ i) (_hi : i < 448) : valid D i := by
  by_cases h416_448 : i < 432
  · by_cases h416_432 : i < 424
    · by_cases h416_424 : i < 420
      · by_cases h416_420 : i < 418
        · by_cases h416_418 : i < 417
          · have e : i = 416 := by omega
            subst i
            exact ok416
          · have e : i = 417 := by omega
            subst i
            exact ok417
        · by_cases h418_420 : i < 419
          · have e : i = 418 := by omega
            subst i
            exact ok418
          · have e : i = 419 := by omega
            subst i
            exact ok419
      · by_cases h420_424 : i < 422
        · by_cases h420_422 : i < 421
          · have e : i = 420 := by omega
            subst i
            exact ok420
          · have e : i = 421 := by omega
            subst i
            exact ok421
        · by_cases h422_424 : i < 423
          · have e : i = 422 := by omega
            subst i
            exact ok422
          · have e : i = 423 := by omega
            subst i
            exact ok423
    · by_cases h424_432 : i < 428
      · by_cases h424_428 : i < 426
        · by_cases h424_426 : i < 425
          · have e : i = 424 := by omega
            subst i
            exact ok424
          · have e : i = 425 := by omega
            subst i
            exact ok425
        · by_cases h426_428 : i < 427
          · have e : i = 426 := by omega
            subst i
            exact ok426
          · have e : i = 427 := by omega
            subst i
            exact ok427
      · by_cases h428_432 : i < 430
        · by_cases h428_430 : i < 429
          · have e : i = 428 := by omega
            subst i
            exact ok428
          · have e : i = 429 := by omega
            subst i
            exact ok429
        · by_cases h430_432 : i < 431
          · have e : i = 430 := by omega
            subst i
            exact ok430
          · have e : i = 431 := by omega
            subst i
            exact ok431
  · by_cases h432_448 : i < 440
    · by_cases h432_440 : i < 436
      · by_cases h432_436 : i < 434
        · by_cases h432_434 : i < 433
          · have e : i = 432 := by omega
            subst i
            exact ok432
          · have e : i = 433 := by omega
            subst i
            exact ok433
        · by_cases h434_436 : i < 435
          · have e : i = 434 := by omega
            subst i
            exact ok434
          · have e : i = 435 := by omega
            subst i
            exact ok435
      · by_cases h436_440 : i < 438
        · by_cases h436_438 : i < 437
          · have e : i = 436 := by omega
            subst i
            exact ok436
          · have e : i = 437 := by omega
            subst i
            exact ok437
        · by_cases h438_440 : i < 439
          · have e : i = 438 := by omega
            subst i
            exact ok438
          · have e : i = 439 := by omega
            subst i
            exact ok439
    · by_cases h440_448 : i < 444
      · by_cases h440_444 : i < 442
        · by_cases h440_442 : i < 441
          · have e : i = 440 := by omega
            subst i
            exact ok440
          · have e : i = 441 := by omega
            subst i
            exact ok441
        · by_cases h442_444 : i < 443
          · have e : i = 442 := by omega
            subst i
            exact ok442
          · have e : i = 443 := by omega
            subst i
            exact ok443
      · by_cases h444_448 : i < 446
        · by_cases h444_446 : i < 445
          · have e : i = 444 := by omega
            subst i
            exact ok444
          · have e : i = 445 := by omega
            subst i
            exact ok445
        · by_cases h446_448 : i < 447
          · have e : i = 446 := by omega
            subst i
            exact ok446
          · have e : i = 447 := by omega
            subst i
            exact ok447
end HaarMetaNineData
