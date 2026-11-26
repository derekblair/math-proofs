import HaarC5Data
namespace HaarC5Data
open HaarC5DAG HaarC5Voltage
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
private theorem ok646 : valid D 646 := by decide +kernel
private theorem ok647 : valid D 647 := by decide +kernel
theorem C624valid (i : Nat) (_lo : 624 ≤ i) (_hi : i < 648) : valid D i := by
  by_cases h624_648 : i < 636
  · by_cases h624_636 : i < 630
    · by_cases h624_630 : i < 627
      · by_cases h624_627 : i < 625
        · have e : i = 624 := by omega
          subst i
          exact ok624
        · by_cases h625_627 : i < 626
          · have e : i = 625 := by omega
            subst i
            exact ok625
          · have e : i = 626 := by omega
            subst i
            exact ok626
      · by_cases h627_630 : i < 628
        · have e : i = 627 := by omega
          subst i
          exact ok627
        · by_cases h628_630 : i < 629
          · have e : i = 628 := by omega
            subst i
            exact ok628
          · have e : i = 629 := by omega
            subst i
            exact ok629
    · by_cases h630_636 : i < 633
      · by_cases h630_633 : i < 631
        · have e : i = 630 := by omega
          subst i
          exact ok630
        · by_cases h631_633 : i < 632
          · have e : i = 631 := by omega
            subst i
            exact ok631
          · have e : i = 632 := by omega
            subst i
            exact ok632
      · by_cases h633_636 : i < 634
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
  · by_cases h636_648 : i < 642
    · by_cases h636_642 : i < 639
      · by_cases h636_639 : i < 637
        · have e : i = 636 := by omega
          subst i
          exact ok636
        · by_cases h637_639 : i < 638
          · have e : i = 637 := by omega
            subst i
            exact ok637
          · have e : i = 638 := by omega
            subst i
            exact ok638
      · by_cases h639_642 : i < 640
        · have e : i = 639 := by omega
          subst i
          exact ok639
        · by_cases h640_642 : i < 641
          · have e : i = 640 := by omega
            subst i
            exact ok640
          · have e : i = 641 := by omega
            subst i
            exact ok641
    · by_cases h642_648 : i < 645
      · by_cases h642_645 : i < 643
        · have e : i = 642 := by omega
          subst i
          exact ok642
        · by_cases h643_645 : i < 644
          · have e : i = 643 := by omega
            subst i
            exact ok643
          · have e : i = 644 := by omega
            subst i
            exact ok644
      · by_cases h645_648 : i < 646
        · have e : i = 645 := by omega
          subst i
          exact ok645
        · by_cases h646_648 : i < 647
          · have e : i = 646 := by omega
            subst i
            exact ok646
          · have e : i = 647 := by omega
            subst i
            exact ok647
end HaarC5Data
