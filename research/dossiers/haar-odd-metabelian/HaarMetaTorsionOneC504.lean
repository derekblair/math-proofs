import HaarMetaTorsionOneData
namespace HaarMetaTorsionOneData
open HaarMetaTorsionOneDAG HaarMetaTorsionOneVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok504 : valid D 504 := by decide +kernel
private theorem ok505 : valid D 505 := by decide +kernel
private theorem ok506 : valid D 506 := by decide +kernel
private theorem ok507 : valid D 507 := by decide +kernel
private theorem ok508 : valid D 508 := by decide +kernel
private theorem ok509 : valid D 509 := by decide +kernel
private theorem ok510 : valid D 510 := by decide +kernel
private theorem ok511 : valid D 511 := by decide +kernel
private theorem ok512 : valid D 512 := by decide +kernel
private theorem ok513 : valid D 513 := by decide +kernel
private theorem ok514 : valid D 514 := by decide +kernel
private theorem ok515 : valid D 515 := by decide +kernel
private theorem ok516 : valid D 516 := by decide +kernel
private theorem ok517 : valid D 517 := by decide +kernel
private theorem ok518 : valid D 518 := by decide +kernel
private theorem ok519 : valid D 519 := by decide +kernel
private theorem ok520 : valid D 520 := by decide +kernel
private theorem ok521 : valid D 521 := by decide +kernel
private theorem ok522 : valid D 522 := by decide +kernel
private theorem ok523 : valid D 523 := by decide +kernel
private theorem ok524 : valid D 524 := by decide +kernel
private theorem ok525 : valid D 525 := by decide +kernel
private theorem ok526 : valid D 526 := by decide +kernel
private theorem ok527 : valid D 527 := by decide +kernel
theorem C504valid (i : Nat) (_lo : 504 ≤ i) (_hi : i < 528) : valid D i := by
  by_cases h504_528 : i < 516
  · by_cases h504_516 : i < 510
    · by_cases h504_510 : i < 507
      · by_cases h504_507 : i < 505
        · have e : i = 504 := by omega
          subst i
          exact ok504
        · by_cases h505_507 : i < 506
          · have e : i = 505 := by omega
            subst i
            exact ok505
          · have e : i = 506 := by omega
            subst i
            exact ok506
      · by_cases h507_510 : i < 508
        · have e : i = 507 := by omega
          subst i
          exact ok507
        · by_cases h508_510 : i < 509
          · have e : i = 508 := by omega
            subst i
            exact ok508
          · have e : i = 509 := by omega
            subst i
            exact ok509
    · by_cases h510_516 : i < 513
      · by_cases h510_513 : i < 511
        · have e : i = 510 := by omega
          subst i
          exact ok510
        · by_cases h511_513 : i < 512
          · have e : i = 511 := by omega
            subst i
            exact ok511
          · have e : i = 512 := by omega
            subst i
            exact ok512
      · by_cases h513_516 : i < 514
        · have e : i = 513 := by omega
          subst i
          exact ok513
        · by_cases h514_516 : i < 515
          · have e : i = 514 := by omega
            subst i
            exact ok514
          · have e : i = 515 := by omega
            subst i
            exact ok515
  · by_cases h516_528 : i < 522
    · by_cases h516_522 : i < 519
      · by_cases h516_519 : i < 517
        · have e : i = 516 := by omega
          subst i
          exact ok516
        · by_cases h517_519 : i < 518
          · have e : i = 517 := by omega
            subst i
            exact ok517
          · have e : i = 518 := by omega
            subst i
            exact ok518
      · by_cases h519_522 : i < 520
        · have e : i = 519 := by omega
          subst i
          exact ok519
        · by_cases h520_522 : i < 521
          · have e : i = 520 := by omega
            subst i
            exact ok520
          · have e : i = 521 := by omega
            subst i
            exact ok521
    · by_cases h522_528 : i < 525
      · by_cases h522_525 : i < 523
        · have e : i = 522 := by omega
          subst i
          exact ok522
        · by_cases h523_525 : i < 524
          · have e : i = 523 := by omega
            subst i
            exact ok523
          · have e : i = 524 := by omega
            subst i
            exact ok524
      · by_cases h525_528 : i < 526
        · have e : i = 525 := by omega
          subst i
          exact ok525
        · by_cases h526_528 : i < 527
          · have e : i = 526 := by omega
            subst i
            exact ok526
          · have e : i = 527 := by omega
            subst i
            exact ok527
end HaarMetaTorsionOneData
