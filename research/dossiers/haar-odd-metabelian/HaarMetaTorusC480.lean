import HaarMetaTorusData
namespace HaarMetaTorusData
open HaarMetaTorusDAG HaarMetaTorusVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok480 : valid D 480 := by decide +kernel
private theorem ok481 : valid D 481 := by decide +kernel
private theorem ok482 : valid D 482 := by decide +kernel
private theorem ok483 : valid D 483 := by decide +kernel
private theorem ok484 : valid D 484 := by decide +kernel
private theorem ok485 : valid D 485 := by decide +kernel
private theorem ok486 : valid D 486 := by decide +kernel
private theorem ok487 : valid D 487 := by decide +kernel
private theorem ok488 : valid D 488 := by decide +kernel
private theorem ok489 : valid D 489 := by decide +kernel
private theorem ok490 : valid D 490 := by decide +kernel
private theorem ok491 : valid D 491 := by decide +kernel
private theorem ok492 : valid D 492 := by decide +kernel
private theorem ok493 : valid D 493 := by decide +kernel
private theorem ok494 : valid D 494 := by decide +kernel
private theorem ok495 : valid D 495 := by decide +kernel
private theorem ok496 : valid D 496 := by decide +kernel
private theorem ok497 : valid D 497 := by decide +kernel
private theorem ok498 : valid D 498 := by decide +kernel
private theorem ok499 : valid D 499 := by decide +kernel
private theorem ok500 : valid D 500 := by decide +kernel
private theorem ok501 : valid D 501 := by decide +kernel
private theorem ok502 : valid D 502 := by decide +kernel
private theorem ok503 : valid D 503 := by decide +kernel
private theorem ok504 : valid D 504 := by decide +kernel
private theorem ok505 : valid D 505 := by decide +kernel
private theorem ok506 : valid D 506 := by decide +kernel
private theorem ok507 : valid D 507 := by decide +kernel
private theorem ok508 : valid D 508 := by decide +kernel
private theorem ok509 : valid D 509 := by decide +kernel
private theorem ok510 : valid D 510 := by decide +kernel
private theorem ok511 : valid D 511 := by decide +kernel
theorem C480valid (i : Nat) (_lo : 480 ≤ i) (_hi : i < 512) : valid D i := by
  by_cases h480_512 : i < 496
  · by_cases h480_496 : i < 488
    · by_cases h480_488 : i < 484
      · by_cases h480_484 : i < 482
        · by_cases h480_482 : i < 481
          · have e : i = 480 := by omega
            subst i
            exact ok480
          · have e : i = 481 := by omega
            subst i
            exact ok481
        · by_cases h482_484 : i < 483
          · have e : i = 482 := by omega
            subst i
            exact ok482
          · have e : i = 483 := by omega
            subst i
            exact ok483
      · by_cases h484_488 : i < 486
        · by_cases h484_486 : i < 485
          · have e : i = 484 := by omega
            subst i
            exact ok484
          · have e : i = 485 := by omega
            subst i
            exact ok485
        · by_cases h486_488 : i < 487
          · have e : i = 486 := by omega
            subst i
            exact ok486
          · have e : i = 487 := by omega
            subst i
            exact ok487
    · by_cases h488_496 : i < 492
      · by_cases h488_492 : i < 490
        · by_cases h488_490 : i < 489
          · have e : i = 488 := by omega
            subst i
            exact ok488
          · have e : i = 489 := by omega
            subst i
            exact ok489
        · by_cases h490_492 : i < 491
          · have e : i = 490 := by omega
            subst i
            exact ok490
          · have e : i = 491 := by omega
            subst i
            exact ok491
      · by_cases h492_496 : i < 494
        · by_cases h492_494 : i < 493
          · have e : i = 492 := by omega
            subst i
            exact ok492
          · have e : i = 493 := by omega
            subst i
            exact ok493
        · by_cases h494_496 : i < 495
          · have e : i = 494 := by omega
            subst i
            exact ok494
          · have e : i = 495 := by omega
            subst i
            exact ok495
  · by_cases h496_512 : i < 504
    · by_cases h496_504 : i < 500
      · by_cases h496_500 : i < 498
        · by_cases h496_498 : i < 497
          · have e : i = 496 := by omega
            subst i
            exact ok496
          · have e : i = 497 := by omega
            subst i
            exact ok497
        · by_cases h498_500 : i < 499
          · have e : i = 498 := by omega
            subst i
            exact ok498
          · have e : i = 499 := by omega
            subst i
            exact ok499
      · by_cases h500_504 : i < 502
        · by_cases h500_502 : i < 501
          · have e : i = 500 := by omega
            subst i
            exact ok500
          · have e : i = 501 := by omega
            subst i
            exact ok501
        · by_cases h502_504 : i < 503
          · have e : i = 502 := by omega
            subst i
            exact ok502
          · have e : i = 503 := by omega
            subst i
            exact ok503
    · by_cases h504_512 : i < 508
      · by_cases h504_508 : i < 506
        · by_cases h504_506 : i < 505
          · have e : i = 504 := by omega
            subst i
            exact ok504
          · have e : i = 505 := by omega
            subst i
            exact ok505
        · by_cases h506_508 : i < 507
          · have e : i = 506 := by omega
            subst i
            exact ok506
          · have e : i = 507 := by omega
            subst i
            exact ok507
      · by_cases h508_512 : i < 510
        · by_cases h508_510 : i < 509
          · have e : i = 508 := by omega
            subst i
            exact ok508
          · have e : i = 509 := by omega
            subst i
            exact ok509
        · by_cases h510_512 : i < 511
          · have e : i = 510 := by omega
            subst i
            exact ok510
          · have e : i = 511 := by omega
            subst i
            exact ok511
end HaarMetaTorusData
