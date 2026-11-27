import HaarMetaNineData
namespace HaarMetaNineData
open HaarMetaNineDAG HaarMetaNineVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
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
private theorem ok528 : valid D 528 := by decide +kernel
private theorem ok529 : valid D 529 := by decide +kernel
private theorem ok530 : valid D 530 := by decide +kernel
private theorem ok531 : valid D 531 := by decide +kernel
private theorem ok532 : valid D 532 := by decide +kernel
private theorem ok533 : valid D 533 := by decide +kernel
private theorem ok534 : valid D 534 := by decide +kernel
private theorem ok535 : valid D 535 := by decide +kernel
private theorem ok536 : valid D 536 := by decide +kernel
private theorem ok537 : valid D 537 := by decide +kernel
private theorem ok538 : valid D 538 := by decide +kernel
private theorem ok539 : valid D 539 := by decide +kernel
private theorem ok540 : valid D 540 := by decide +kernel
private theorem ok541 : valid D 541 := by decide +kernel
private theorem ok542 : valid D 542 := by decide +kernel
private theorem ok543 : valid D 543 := by decide +kernel
theorem C512valid (i : Nat) (_lo : 512 ≤ i) (_hi : i < 544) : valid D i := by
  by_cases h512_544 : i < 528
  · by_cases h512_528 : i < 520
    · by_cases h512_520 : i < 516
      · by_cases h512_516 : i < 514
        · by_cases h512_514 : i < 513
          · have e : i = 512 := by omega
            subst i
            exact ok512
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
      · by_cases h516_520 : i < 518
        · by_cases h516_518 : i < 517
          · have e : i = 516 := by omega
            subst i
            exact ok516
          · have e : i = 517 := by omega
            subst i
            exact ok517
        · by_cases h518_520 : i < 519
          · have e : i = 518 := by omega
            subst i
            exact ok518
          · have e : i = 519 := by omega
            subst i
            exact ok519
    · by_cases h520_528 : i < 524
      · by_cases h520_524 : i < 522
        · by_cases h520_522 : i < 521
          · have e : i = 520 := by omega
            subst i
            exact ok520
          · have e : i = 521 := by omega
            subst i
            exact ok521
        · by_cases h522_524 : i < 523
          · have e : i = 522 := by omega
            subst i
            exact ok522
          · have e : i = 523 := by omega
            subst i
            exact ok523
      · by_cases h524_528 : i < 526
        · by_cases h524_526 : i < 525
          · have e : i = 524 := by omega
            subst i
            exact ok524
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
  · by_cases h528_544 : i < 536
    · by_cases h528_536 : i < 532
      · by_cases h528_532 : i < 530
        · by_cases h528_530 : i < 529
          · have e : i = 528 := by omega
            subst i
            exact ok528
          · have e : i = 529 := by omega
            subst i
            exact ok529
        · by_cases h530_532 : i < 531
          · have e : i = 530 := by omega
            subst i
            exact ok530
          · have e : i = 531 := by omega
            subst i
            exact ok531
      · by_cases h532_536 : i < 534
        · by_cases h532_534 : i < 533
          · have e : i = 532 := by omega
            subst i
            exact ok532
          · have e : i = 533 := by omega
            subst i
            exact ok533
        · by_cases h534_536 : i < 535
          · have e : i = 534 := by omega
            subst i
            exact ok534
          · have e : i = 535 := by omega
            subst i
            exact ok535
    · by_cases h536_544 : i < 540
      · by_cases h536_540 : i < 538
        · by_cases h536_538 : i < 537
          · have e : i = 536 := by omega
            subst i
            exact ok536
          · have e : i = 537 := by omega
            subst i
            exact ok537
        · by_cases h538_540 : i < 539
          · have e : i = 538 := by omega
            subst i
            exact ok538
          · have e : i = 539 := by omega
            subst i
            exact ok539
      · by_cases h540_544 : i < 542
        · by_cases h540_542 : i < 541
          · have e : i = 540 := by omega
            subst i
            exact ok540
          · have e : i = 541 := by omega
            subst i
            exact ok541
        · by_cases h542_544 : i < 543
          · have e : i = 542 := by omega
            subst i
            exact ok542
          · have e : i = 543 := by omega
            subst i
            exact ok543
end HaarMetaNineData
