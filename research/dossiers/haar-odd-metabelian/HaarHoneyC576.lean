import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok576 : valid D 576 := by decide +kernel
private theorem ok577 : valid D 577 := by decide +kernel
private theorem ok578 : valid D 578 := by decide +kernel
private theorem ok579 : valid D 579 := by decide +kernel
private theorem ok580 : valid D 580 := by decide +kernel
private theorem ok581 : valid D 581 := by decide +kernel
private theorem ok582 : valid D 582 := by decide +kernel
private theorem ok583 : valid D 583 := by decide +kernel
private theorem ok584 : valid D 584 := by decide +kernel
private theorem ok585 : valid D 585 := by decide +kernel
private theorem ok586 : valid D 586 := by decide +kernel
private theorem ok587 : valid D 587 := by decide +kernel
private theorem ok588 : valid D 588 := by decide +kernel
private theorem ok589 : valid D 589 := by decide +kernel
private theorem ok590 : valid D 590 := by decide +kernel
private theorem ok591 : valid D 591 := by decide +kernel
private theorem ok592 : valid D 592 := by decide +kernel
private theorem ok593 : valid D 593 := by decide +kernel
private theorem ok594 : valid D 594 := by decide +kernel
private theorem ok595 : valid D 595 := by decide +kernel
private theorem ok596 : valid D 596 := by decide +kernel
private theorem ok597 : valid D 597 := by decide +kernel
private theorem ok598 : valid D 598 := by decide +kernel
private theorem ok599 : valid D 599 := by decide +kernel
theorem C576valid (i : Nat) (_lo : 576 ≤ i) (_hi : i < 600) : valid D i := by
  by_cases h576_600 : i < 588
  · by_cases h576_588 : i < 582
    · by_cases h576_582 : i < 579
      · by_cases h576_579 : i < 577
        · have e : i = 576 := by omega
          subst i
          exact ok576
        · by_cases h577_579 : i < 578
          · have e : i = 577 := by omega
            subst i
            exact ok577
          · have e : i = 578 := by omega
            subst i
            exact ok578
      · by_cases h579_582 : i < 580
        · have e : i = 579 := by omega
          subst i
          exact ok579
        · by_cases h580_582 : i < 581
          · have e : i = 580 := by omega
            subst i
            exact ok580
          · have e : i = 581 := by omega
            subst i
            exact ok581
    · by_cases h582_588 : i < 585
      · by_cases h582_585 : i < 583
        · have e : i = 582 := by omega
          subst i
          exact ok582
        · by_cases h583_585 : i < 584
          · have e : i = 583 := by omega
            subst i
            exact ok583
          · have e : i = 584 := by omega
            subst i
            exact ok584
      · by_cases h585_588 : i < 586
        · have e : i = 585 := by omega
          subst i
          exact ok585
        · by_cases h586_588 : i < 587
          · have e : i = 586 := by omega
            subst i
            exact ok586
          · have e : i = 587 := by omega
            subst i
            exact ok587
  · by_cases h588_600 : i < 594
    · by_cases h588_594 : i < 591
      · by_cases h588_591 : i < 589
        · have e : i = 588 := by omega
          subst i
          exact ok588
        · by_cases h589_591 : i < 590
          · have e : i = 589 := by omega
            subst i
            exact ok589
          · have e : i = 590 := by omega
            subst i
            exact ok590
      · by_cases h591_594 : i < 592
        · have e : i = 591 := by omega
          subst i
          exact ok591
        · by_cases h592_594 : i < 593
          · have e : i = 592 := by omega
            subst i
            exact ok592
          · have e : i = 593 := by omega
            subst i
            exact ok593
    · by_cases h594_600 : i < 597
      · by_cases h594_597 : i < 595
        · have e : i = 594 := by omega
          subst i
          exact ok594
        · by_cases h595_597 : i < 596
          · have e : i = 595 := by omega
            subst i
            exact ok595
          · have e : i = 596 := by omega
            subst i
            exact ok596
      · by_cases h597_600 : i < 598
        · have e : i = 597 := by omega
          subst i
          exact ok597
        · by_cases h598_600 : i < 599
          · have e : i = 598 := by omega
            subst i
            exact ok598
          · have e : i = 599 := by omega
            subst i
            exact ok599
end HaarHoneyData
