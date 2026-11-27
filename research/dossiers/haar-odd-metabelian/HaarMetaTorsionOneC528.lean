import HaarMetaTorsionOneData
namespace HaarMetaTorsionOneData
open HaarMetaTorsionOneDAG HaarMetaTorsionOneVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
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
private theorem ok544 : valid D 544 := by decide +kernel
private theorem ok545 : valid D 545 := by decide +kernel
private theorem ok546 : valid D 546 := by decide +kernel
private theorem ok547 : valid D 547 := by decide +kernel
private theorem ok548 : valid D 548 := by decide +kernel
private theorem ok549 : valid D 549 := by decide +kernel
private theorem ok550 : valid D 550 := by decide +kernel
private theorem ok551 : valid D 551 := by decide +kernel
theorem C528valid (i : Nat) (_lo : 528 ≤ i) (_hi : i < 552) : valid D i := by
  by_cases h528_552 : i < 540
  · by_cases h528_540 : i < 534
    · by_cases h528_534 : i < 531
      · by_cases h528_531 : i < 529
        · have e : i = 528 := by omega
          subst i
          exact ok528
        · by_cases h529_531 : i < 530
          · have e : i = 529 := by omega
            subst i
            exact ok529
          · have e : i = 530 := by omega
            subst i
            exact ok530
      · by_cases h531_534 : i < 532
        · have e : i = 531 := by omega
          subst i
          exact ok531
        · by_cases h532_534 : i < 533
          · have e : i = 532 := by omega
            subst i
            exact ok532
          · have e : i = 533 := by omega
            subst i
            exact ok533
    · by_cases h534_540 : i < 537
      · by_cases h534_537 : i < 535
        · have e : i = 534 := by omega
          subst i
          exact ok534
        · by_cases h535_537 : i < 536
          · have e : i = 535 := by omega
            subst i
            exact ok535
          · have e : i = 536 := by omega
            subst i
            exact ok536
      · by_cases h537_540 : i < 538
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
  · by_cases h540_552 : i < 546
    · by_cases h540_546 : i < 543
      · by_cases h540_543 : i < 541
        · have e : i = 540 := by omega
          subst i
          exact ok540
        · by_cases h541_543 : i < 542
          · have e : i = 541 := by omega
            subst i
            exact ok541
          · have e : i = 542 := by omega
            subst i
            exact ok542
      · by_cases h543_546 : i < 544
        · have e : i = 543 := by omega
          subst i
          exact ok543
        · by_cases h544_546 : i < 545
          · have e : i = 544 := by omega
            subst i
            exact ok544
          · have e : i = 545 := by omega
            subst i
            exact ok545
    · by_cases h546_552 : i < 549
      · by_cases h546_549 : i < 547
        · have e : i = 546 := by omega
          subst i
          exact ok546
        · by_cases h547_549 : i < 548
          · have e : i = 547 := by omega
            subst i
            exact ok547
          · have e : i = 548 := by omega
            subst i
            exact ok548
      · by_cases h549_552 : i < 550
        · have e : i = 549 := by omega
          subst i
          exact ok549
        · by_cases h550_552 : i < 551
          · have e : i = 550 := by omega
            subst i
            exact ok550
          · have e : i = 551 := by omega
            subst i
            exact ok551
end HaarMetaTorsionOneData
