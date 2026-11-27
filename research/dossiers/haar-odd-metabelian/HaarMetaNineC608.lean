import HaarMetaNineData
namespace HaarMetaNineData
open HaarMetaNineDAG HaarMetaNineVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok608 : valid D 608 := by decide +kernel
private theorem ok609 : valid D 609 := by decide +kernel
private theorem ok610 : valid D 610 := by decide +kernel
private theorem ok611 : valid D 611 := by decide +kernel
private theorem ok612 : valid D 612 := by decide +kernel
private theorem ok613 : valid D 613 := by decide +kernel
private theorem ok614 : valid D 614 := by decide +kernel
private theorem ok615 : valid D 615 := by decide +kernel
private theorem ok616 : valid D 616 := by decide +kernel
private theorem ok617 : valid D 617 := by decide +kernel
private theorem ok618 : valid D 618 := by decide +kernel
private theorem ok619 : valid D 619 := by decide +kernel
private theorem ok620 : valid D 620 := by decide +kernel
private theorem ok621 : valid D 621 := by decide +kernel
private theorem ok622 : valid D 622 := by decide +kernel
private theorem ok623 : valid D 623 := by decide +kernel
private theorem ok624 : valid D 624 := by decide +kernel
private theorem ok625 : valid D 625 := by decide +kernel
private theorem ok626 : valid D 626 := by decide +kernel
private theorem ok627 : valid D 627 := by decide +kernel
private theorem ok628 : valid D 628 := by decide +kernel
private theorem ok629 : valid D 629 := by decide +kernel
private theorem ok630 : valid D 630 := by decide +kernel
private theorem ok631 : valid D 631 := by decide +kernel
private theorem ok632 : valid D 632 := by decide +kernel
private theorem ok633 : valid D 633 := by decide +kernel
private theorem ok634 : valid D 634 := by decide +kernel
private theorem ok635 : valid D 635 := by decide +kernel
private theorem ok636 : valid D 636 := by decide +kernel
private theorem ok637 : valid D 637 := by decide +kernel
private theorem ok638 : valid D 638 := by decide +kernel
private theorem ok639 : valid D 639 := by decide +kernel
theorem C608valid (i : Nat) (_lo : 608 ≤ i) (_hi : i < 640) : valid D i := by
  by_cases h608_640 : i < 624
  · by_cases h608_624 : i < 616
    · by_cases h608_616 : i < 612
      · by_cases h608_612 : i < 610
        · by_cases h608_610 : i < 609
          · have e : i = 608 := by omega
            subst i
            exact ok608
          · have e : i = 609 := by omega
            subst i
            exact ok609
        · by_cases h610_612 : i < 611
          · have e : i = 610 := by omega
            subst i
            exact ok610
          · have e : i = 611 := by omega
            subst i
            exact ok611
      · by_cases h612_616 : i < 614
        · by_cases h612_614 : i < 613
          · have e : i = 612 := by omega
            subst i
            exact ok612
          · have e : i = 613 := by omega
            subst i
            exact ok613
        · by_cases h614_616 : i < 615
          · have e : i = 614 := by omega
            subst i
            exact ok614
          · have e : i = 615 := by omega
            subst i
            exact ok615
    · by_cases h616_624 : i < 620
      · by_cases h616_620 : i < 618
        · by_cases h616_618 : i < 617
          · have e : i = 616 := by omega
            subst i
            exact ok616
          · have e : i = 617 := by omega
            subst i
            exact ok617
        · by_cases h618_620 : i < 619
          · have e : i = 618 := by omega
            subst i
            exact ok618
          · have e : i = 619 := by omega
            subst i
            exact ok619
      · by_cases h620_624 : i < 622
        · by_cases h620_622 : i < 621
          · have e : i = 620 := by omega
            subst i
            exact ok620
          · have e : i = 621 := by omega
            subst i
            exact ok621
        · by_cases h622_624 : i < 623
          · have e : i = 622 := by omega
            subst i
            exact ok622
          · have e : i = 623 := by omega
            subst i
            exact ok623
  · by_cases h624_640 : i < 632
    · by_cases h624_632 : i < 628
      · by_cases h624_628 : i < 626
        · by_cases h624_626 : i < 625
          · have e : i = 624 := by omega
            subst i
            exact ok624
          · have e : i = 625 := by omega
            subst i
            exact ok625
        · by_cases h626_628 : i < 627
          · have e : i = 626 := by omega
            subst i
            exact ok626
          · have e : i = 627 := by omega
            subst i
            exact ok627
      · by_cases h628_632 : i < 630
        · by_cases h628_630 : i < 629
          · have e : i = 628 := by omega
            subst i
            exact ok628
          · have e : i = 629 := by omega
            subst i
            exact ok629
        · by_cases h630_632 : i < 631
          · have e : i = 630 := by omega
            subst i
            exact ok630
          · have e : i = 631 := by omega
            subst i
            exact ok631
    · by_cases h632_640 : i < 636
      · by_cases h632_636 : i < 634
        · by_cases h632_634 : i < 633
          · have e : i = 632 := by omega
            subst i
            exact ok632
          · have e : i = 633 := by omega
            subst i
            exact ok633
        · by_cases h634_636 : i < 635
          · have e : i = 634 := by omega
            subst i
            exact ok634
          · have e : i = 635 := by omega
            subst i
            exact ok635
      · by_cases h636_640 : i < 638
        · by_cases h636_638 : i < 637
          · have e : i = 636 := by omega
            subst i
            exact ok636
          · have e : i = 637 := by omega
            subst i
            exact ok637
        · by_cases h638_640 : i < 639
          · have e : i = 638 := by omega
            subst i
            exact ok638
          · have e : i = 639 := by omega
            subst i
            exact ok639
end HaarMetaNineData
