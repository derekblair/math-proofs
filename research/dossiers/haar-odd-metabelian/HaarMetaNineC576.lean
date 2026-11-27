import HaarMetaNineData
namespace HaarMetaNineData
open HaarMetaNineDAG HaarMetaNineVoltage
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
private theorem ok600 : valid D 600 := by decide +kernel
private theorem ok601 : valid D 601 := by decide +kernel
private theorem ok602 : valid D 602 := by decide +kernel
private theorem ok603 : valid D 603 := by decide +kernel
private theorem ok604 : valid D 604 := by decide +kernel
private theorem ok605 : valid D 605 := by decide +kernel
private theorem ok606 : valid D 606 := by decide +kernel
private theorem ok607 : valid D 607 := by decide +kernel
theorem C576valid (i : Nat) (_lo : 576 ≤ i) (_hi : i < 608) : valid D i := by
  by_cases h576_608 : i < 592
  · by_cases h576_592 : i < 584
    · by_cases h576_584 : i < 580
      · by_cases h576_580 : i < 578
        · by_cases h576_578 : i < 577
          · have e : i = 576 := by omega
            subst i
            exact ok576
          · have e : i = 577 := by omega
            subst i
            exact ok577
        · by_cases h578_580 : i < 579
          · have e : i = 578 := by omega
            subst i
            exact ok578
          · have e : i = 579 := by omega
            subst i
            exact ok579
      · by_cases h580_584 : i < 582
        · by_cases h580_582 : i < 581
          · have e : i = 580 := by omega
            subst i
            exact ok580
          · have e : i = 581 := by omega
            subst i
            exact ok581
        · by_cases h582_584 : i < 583
          · have e : i = 582 := by omega
            subst i
            exact ok582
          · have e : i = 583 := by omega
            subst i
            exact ok583
    · by_cases h584_592 : i < 588
      · by_cases h584_588 : i < 586
        · by_cases h584_586 : i < 585
          · have e : i = 584 := by omega
            subst i
            exact ok584
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
      · by_cases h588_592 : i < 590
        · by_cases h588_590 : i < 589
          · have e : i = 588 := by omega
            subst i
            exact ok588
          · have e : i = 589 := by omega
            subst i
            exact ok589
        · by_cases h590_592 : i < 591
          · have e : i = 590 := by omega
            subst i
            exact ok590
          · have e : i = 591 := by omega
            subst i
            exact ok591
  · by_cases h592_608 : i < 600
    · by_cases h592_600 : i < 596
      · by_cases h592_596 : i < 594
        · by_cases h592_594 : i < 593
          · have e : i = 592 := by omega
            subst i
            exact ok592
          · have e : i = 593 := by omega
            subst i
            exact ok593
        · by_cases h594_596 : i < 595
          · have e : i = 594 := by omega
            subst i
            exact ok594
          · have e : i = 595 := by omega
            subst i
            exact ok595
      · by_cases h596_600 : i < 598
        · by_cases h596_598 : i < 597
          · have e : i = 596 := by omega
            subst i
            exact ok596
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
    · by_cases h600_608 : i < 604
      · by_cases h600_604 : i < 602
        · by_cases h600_602 : i < 601
          · have e : i = 600 := by omega
            subst i
            exact ok600
          · have e : i = 601 := by omega
            subst i
            exact ok601
        · by_cases h602_604 : i < 603
          · have e : i = 602 := by omega
            subst i
            exact ok602
          · have e : i = 603 := by omega
            subst i
            exact ok603
      · by_cases h604_608 : i < 606
        · by_cases h604_606 : i < 605
          · have e : i = 604 := by omega
            subst i
            exact ok604
          · have e : i = 605 := by omega
            subst i
            exact ok605
        · by_cases h606_608 : i < 607
          · have e : i = 606 := by omega
            subst i
            exact ok606
          · have e : i = 607 := by omega
            subst i
            exact ok607
end HaarMetaNineData
