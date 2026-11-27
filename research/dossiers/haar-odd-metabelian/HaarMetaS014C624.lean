import HaarMetaS014Data
namespace HaarMetaS014Data
open HaarMetaS014DAG HaarMetaS014Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
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
private theorem ok640 : valid D 640 := by decide +kernel
private theorem ok641 : valid D 641 := by decide +kernel
private theorem ok642 : valid D 642 := by decide +kernel
private theorem ok643 : valid D 643 := by decide +kernel
private theorem ok644 : valid D 644 := by decide +kernel
private theorem ok645 : valid D 645 := by decide +kernel
theorem C624valid (i : Nat) (_lo : 624 ≤ i) (_hi : i < 646) : valid D i := by
  by_cases h624_646 : i < 635
  · by_cases h624_635 : i < 629
    · by_cases h624_629 : i < 626
      · by_cases h624_626 : i < 625
        · have e : i = 624 := by omega
          subst i
          exact ok624
        · have e : i = 625 := by omega
          subst i
          exact ok625
      · by_cases h626_629 : i < 627
        · have e : i = 626 := by omega
          subst i
          exact ok626
        · by_cases h627_629 : i < 628
          · have e : i = 627 := by omega
            subst i
            exact ok627
          · have e : i = 628 := by omega
            subst i
            exact ok628
    · by_cases h629_635 : i < 632
      · by_cases h629_632 : i < 630
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
      · by_cases h632_635 : i < 633
        · have e : i = 632 := by omega
          subst i
          exact ok632
        · by_cases h633_635 : i < 634
          · have e : i = 633 := by omega
            subst i
            exact ok633
          · have e : i = 634 := by omega
            subst i
            exact ok634
  · by_cases h635_646 : i < 640
    · by_cases h635_640 : i < 637
      · by_cases h635_637 : i < 636
        · have e : i = 635 := by omega
          subst i
          exact ok635
        · have e : i = 636 := by omega
          subst i
          exact ok636
      · by_cases h637_640 : i < 638
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
    · by_cases h640_646 : i < 643
      · by_cases h640_643 : i < 641
        · have e : i = 640 := by omega
          subst i
          exact ok640
        · by_cases h641_643 : i < 642
          · have e : i = 641 := by omega
            subst i
            exact ok641
          · have e : i = 642 := by omega
            subst i
            exact ok642
      · by_cases h643_646 : i < 644
        · have e : i = 643 := by omega
          subst i
          exact ok643
        · by_cases h644_646 : i < 645
          · have e : i = 644 := by omega
            subst i
            exact ok644
          · have e : i = 645 := by omega
            subst i
            exact ok645
end HaarMetaS014Data
