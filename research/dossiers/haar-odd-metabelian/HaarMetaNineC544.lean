import HaarMetaNineData
namespace HaarMetaNineData
open HaarMetaNineDAG HaarMetaNineVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok544 : valid D 544 := by decide +kernel
private theorem ok545 : valid D 545 := by decide +kernel
private theorem ok546 : valid D 546 := by decide +kernel
private theorem ok547 : valid D 547 := by decide +kernel
private theorem ok548 : valid D 548 := by decide +kernel
private theorem ok549 : valid D 549 := by decide +kernel
private theorem ok550 : valid D 550 := by decide +kernel
private theorem ok551 : valid D 551 := by decide +kernel
private theorem ok552 : valid D 552 := by decide +kernel
private theorem ok553 : valid D 553 := by decide +kernel
private theorem ok554 : valid D 554 := by decide +kernel
private theorem ok555 : valid D 555 := by decide +kernel
private theorem ok556 : valid D 556 := by decide +kernel
private theorem ok557 : valid D 557 := by decide +kernel
private theorem ok558 : valid D 558 := by decide +kernel
private theorem ok559 : valid D 559 := by decide +kernel
private theorem ok560 : valid D 560 := by decide +kernel
private theorem ok561 : valid D 561 := by decide +kernel
private theorem ok562 : valid D 562 := by decide +kernel
private theorem ok563 : valid D 563 := by decide +kernel
private theorem ok564 : valid D 564 := by decide +kernel
private theorem ok565 : valid D 565 := by decide +kernel
private theorem ok566 : valid D 566 := by decide +kernel
private theorem ok567 : valid D 567 := by decide +kernel
private theorem ok568 : valid D 568 := by decide +kernel
private theorem ok569 : valid D 569 := by decide +kernel
private theorem ok570 : valid D 570 := by decide +kernel
private theorem ok571 : valid D 571 := by decide +kernel
private theorem ok572 : valid D 572 := by decide +kernel
private theorem ok573 : valid D 573 := by decide +kernel
private theorem ok574 : valid D 574 := by decide +kernel
private theorem ok575 : valid D 575 := by decide +kernel
theorem C544valid (i : Nat) (_lo : 544 ≤ i) (_hi : i < 576) : valid D i := by
  by_cases h544_576 : i < 560
  · by_cases h544_560 : i < 552
    · by_cases h544_552 : i < 548
      · by_cases h544_548 : i < 546
        · by_cases h544_546 : i < 545
          · have e : i = 544 := by omega
            subst i
            exact ok544
          · have e : i = 545 := by omega
            subst i
            exact ok545
        · by_cases h546_548 : i < 547
          · have e : i = 546 := by omega
            subst i
            exact ok546
          · have e : i = 547 := by omega
            subst i
            exact ok547
      · by_cases h548_552 : i < 550
        · by_cases h548_550 : i < 549
          · have e : i = 548 := by omega
            subst i
            exact ok548
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
    · by_cases h552_560 : i < 556
      · by_cases h552_556 : i < 554
        · by_cases h552_554 : i < 553
          · have e : i = 552 := by omega
            subst i
            exact ok552
          · have e : i = 553 := by omega
            subst i
            exact ok553
        · by_cases h554_556 : i < 555
          · have e : i = 554 := by omega
            subst i
            exact ok554
          · have e : i = 555 := by omega
            subst i
            exact ok555
      · by_cases h556_560 : i < 558
        · by_cases h556_558 : i < 557
          · have e : i = 556 := by omega
            subst i
            exact ok556
          · have e : i = 557 := by omega
            subst i
            exact ok557
        · by_cases h558_560 : i < 559
          · have e : i = 558 := by omega
            subst i
            exact ok558
          · have e : i = 559 := by omega
            subst i
            exact ok559
  · by_cases h560_576 : i < 568
    · by_cases h560_568 : i < 564
      · by_cases h560_564 : i < 562
        · by_cases h560_562 : i < 561
          · have e : i = 560 := by omega
            subst i
            exact ok560
          · have e : i = 561 := by omega
            subst i
            exact ok561
        · by_cases h562_564 : i < 563
          · have e : i = 562 := by omega
            subst i
            exact ok562
          · have e : i = 563 := by omega
            subst i
            exact ok563
      · by_cases h564_568 : i < 566
        · by_cases h564_566 : i < 565
          · have e : i = 564 := by omega
            subst i
            exact ok564
          · have e : i = 565 := by omega
            subst i
            exact ok565
        · by_cases h566_568 : i < 567
          · have e : i = 566 := by omega
            subst i
            exact ok566
          · have e : i = 567 := by omega
            subst i
            exact ok567
    · by_cases h568_576 : i < 572
      · by_cases h568_572 : i < 570
        · by_cases h568_570 : i < 569
          · have e : i = 568 := by omega
            subst i
            exact ok568
          · have e : i = 569 := by omega
            subst i
            exact ok569
        · by_cases h570_572 : i < 571
          · have e : i = 570 := by omega
            subst i
            exact ok570
          · have e : i = 571 := by omega
            subst i
            exact ok571
      · by_cases h572_576 : i < 574
        · by_cases h572_574 : i < 573
          · have e : i = 572 := by omega
            subst i
            exact ok572
          · have e : i = 573 := by omega
            subst i
            exact ok573
        · by_cases h574_576 : i < 575
          · have e : i = 574 := by omega
            subst i
            exact ok574
          · have e : i = 575 := by omega
            subst i
            exact ok575
end HaarMetaNineData
