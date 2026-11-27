import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
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
theorem C552valid (i : Nat) (_lo : 552 ≤ i) (_hi : i < 576) : valid D i := by
  by_cases h552_576 : i < 564
  · by_cases h552_564 : i < 558
    · by_cases h552_558 : i < 555
      · by_cases h552_555 : i < 553
        · have e : i = 552 := by omega
          subst i
          exact ok552
        · by_cases h553_555 : i < 554
          · have e : i = 553 := by omega
            subst i
            exact ok553
          · have e : i = 554 := by omega
            subst i
            exact ok554
      · by_cases h555_558 : i < 556
        · have e : i = 555 := by omega
          subst i
          exact ok555
        · by_cases h556_558 : i < 557
          · have e : i = 556 := by omega
            subst i
            exact ok556
          · have e : i = 557 := by omega
            subst i
            exact ok557
    · by_cases h558_564 : i < 561
      · by_cases h558_561 : i < 559
        · have e : i = 558 := by omega
          subst i
          exact ok558
        · by_cases h559_561 : i < 560
          · have e : i = 559 := by omega
            subst i
            exact ok559
          · have e : i = 560 := by omega
            subst i
            exact ok560
      · by_cases h561_564 : i < 562
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
  · by_cases h564_576 : i < 570
    · by_cases h564_570 : i < 567
      · by_cases h564_567 : i < 565
        · have e : i = 564 := by omega
          subst i
          exact ok564
        · by_cases h565_567 : i < 566
          · have e : i = 565 := by omega
            subst i
            exact ok565
          · have e : i = 566 := by omega
            subst i
            exact ok566
      · by_cases h567_570 : i < 568
        · have e : i = 567 := by omega
          subst i
          exact ok567
        · by_cases h568_570 : i < 569
          · have e : i = 568 := by omega
            subst i
            exact ok568
          · have e : i = 569 := by omega
            subst i
            exact ok569
    · by_cases h570_576 : i < 573
      · by_cases h570_573 : i < 571
        · have e : i = 570 := by omega
          subst i
          exact ok570
        · by_cases h571_573 : i < 572
          · have e : i = 571 := by omega
            subst i
            exact ok571
          · have e : i = 572 := by omega
            subst i
            exact ok572
      · by_cases h573_576 : i < 574
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
end HaarHoneyData
