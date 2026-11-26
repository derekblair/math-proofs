import HaarMetaS014Data
namespace HaarMetaS014Data
open HaarMetaS014DAG HaarMetaS014Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
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
private theorem ok448 : valid D 448 := by decide +kernel
private theorem ok449 : valid D 449 := by decide +kernel
private theorem ok450 : valid D 450 := by decide +kernel
private theorem ok451 : valid D 451 := by decide +kernel
private theorem ok452 : valid D 452 := by decide +kernel
private theorem ok453 : valid D 453 := by decide +kernel
private theorem ok454 : valid D 454 := by decide +kernel
private theorem ok455 : valid D 455 := by decide +kernel
theorem C432valid (i : Nat) (_lo : 432 ≤ i) (_hi : i < 456) : valid D i := by
  by_cases h432_456 : i < 444
  · by_cases h432_444 : i < 438
    · by_cases h432_438 : i < 435
      · by_cases h432_435 : i < 433
        · have e : i = 432 := by omega
          subst i
          exact ok432
        · by_cases h433_435 : i < 434
          · have e : i = 433 := by omega
            subst i
            exact ok433
          · have e : i = 434 := by omega
            subst i
            exact ok434
      · by_cases h435_438 : i < 436
        · have e : i = 435 := by omega
          subst i
          exact ok435
        · by_cases h436_438 : i < 437
          · have e : i = 436 := by omega
            subst i
            exact ok436
          · have e : i = 437 := by omega
            subst i
            exact ok437
    · by_cases h438_444 : i < 441
      · by_cases h438_441 : i < 439
        · have e : i = 438 := by omega
          subst i
          exact ok438
        · by_cases h439_441 : i < 440
          · have e : i = 439 := by omega
            subst i
            exact ok439
          · have e : i = 440 := by omega
            subst i
            exact ok440
      · by_cases h441_444 : i < 442
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
  · by_cases h444_456 : i < 450
    · by_cases h444_450 : i < 447
      · by_cases h444_447 : i < 445
        · have e : i = 444 := by omega
          subst i
          exact ok444
        · by_cases h445_447 : i < 446
          · have e : i = 445 := by omega
            subst i
            exact ok445
          · have e : i = 446 := by omega
            subst i
            exact ok446
      · by_cases h447_450 : i < 448
        · have e : i = 447 := by omega
          subst i
          exact ok447
        · by_cases h448_450 : i < 449
          · have e : i = 448 := by omega
            subst i
            exact ok448
          · have e : i = 449 := by omega
            subst i
            exact ok449
    · by_cases h450_456 : i < 453
      · by_cases h450_453 : i < 451
        · have e : i = 450 := by omega
          subst i
          exact ok450
        · by_cases h451_453 : i < 452
          · have e : i = 451 := by omega
            subst i
            exact ok451
          · have e : i = 452 := by omega
            subst i
            exact ok452
      · by_cases h453_456 : i < 454
        · have e : i = 453 := by omega
          subst i
          exact ok453
        · by_cases h454_456 : i < 455
          · have e : i = 454 := by omega
            subst i
            exact ok454
          · have e : i = 455 := by omega
            subst i
            exact ok455
end HaarMetaS014Data
