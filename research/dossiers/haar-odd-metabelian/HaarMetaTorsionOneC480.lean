import HaarMetaTorsionOneData
namespace HaarMetaTorsionOneData
open HaarMetaTorsionOneDAG HaarMetaTorsionOneVoltage
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
theorem C480valid (i : Nat) (_lo : 480 ≤ i) (_hi : i < 504) : valid D i := by
  by_cases h480_504 : i < 492
  · by_cases h480_492 : i < 486
    · by_cases h480_486 : i < 483
      · by_cases h480_483 : i < 481
        · have e : i = 480 := by omega
          subst i
          exact ok480
        · by_cases h481_483 : i < 482
          · have e : i = 481 := by omega
            subst i
            exact ok481
          · have e : i = 482 := by omega
            subst i
            exact ok482
      · by_cases h483_486 : i < 484
        · have e : i = 483 := by omega
          subst i
          exact ok483
        · by_cases h484_486 : i < 485
          · have e : i = 484 := by omega
            subst i
            exact ok484
          · have e : i = 485 := by omega
            subst i
            exact ok485
    · by_cases h486_492 : i < 489
      · by_cases h486_489 : i < 487
        · have e : i = 486 := by omega
          subst i
          exact ok486
        · by_cases h487_489 : i < 488
          · have e : i = 487 := by omega
            subst i
            exact ok487
          · have e : i = 488 := by omega
            subst i
            exact ok488
      · by_cases h489_492 : i < 490
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
  · by_cases h492_504 : i < 498
    · by_cases h492_498 : i < 495
      · by_cases h492_495 : i < 493
        · have e : i = 492 := by omega
          subst i
          exact ok492
        · by_cases h493_495 : i < 494
          · have e : i = 493 := by omega
            subst i
            exact ok493
          · have e : i = 494 := by omega
            subst i
            exact ok494
      · by_cases h495_498 : i < 496
        · have e : i = 495 := by omega
          subst i
          exact ok495
        · by_cases h496_498 : i < 497
          · have e : i = 496 := by omega
            subst i
            exact ok496
          · have e : i = 497 := by omega
            subst i
            exact ok497
    · by_cases h498_504 : i < 501
      · by_cases h498_501 : i < 499
        · have e : i = 498 := by omega
          subst i
          exact ok498
        · by_cases h499_501 : i < 500
          · have e : i = 499 := by omega
            subst i
            exact ok499
          · have e : i = 500 := by omega
            subst i
            exact ok500
      · by_cases h501_504 : i < 502
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
end HaarMetaTorsionOneData
