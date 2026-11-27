import HaarMetaNineData
namespace HaarMetaNineData
open HaarMetaNineDAG HaarMetaNineVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok640 : valid D 640 := by decide +kernel
private theorem ok641 : valid D 641 := by decide +kernel
private theorem ok642 : valid D 642 := by decide +kernel
private theorem ok643 : valid D 643 := by decide +kernel
private theorem ok644 : valid D 644 := by decide +kernel
private theorem ok645 : valid D 645 := by decide +kernel
private theorem ok646 : valid D 646 := by decide +kernel
private theorem ok647 : valid D 647 := by decide +kernel
private theorem ok648 : valid D 648 := by decide +kernel
private theorem ok649 : valid D 649 := by decide +kernel
private theorem ok650 : valid D 650 := by decide +kernel
private theorem ok651 : valid D 651 := by decide +kernel
private theorem ok652 : valid D 652 := by decide +kernel
private theorem ok653 : valid D 653 := by decide +kernel
private theorem ok654 : valid D 654 := by decide +kernel
private theorem ok655 : valid D 655 := by decide +kernel
private theorem ok656 : valid D 656 := by decide +kernel
private theorem ok657 : valid D 657 := by decide +kernel
private theorem ok658 : valid D 658 := by decide +kernel
private theorem ok659 : valid D 659 := by decide +kernel
private theorem ok660 : valid D 660 := by decide +kernel
private theorem ok661 : valid D 661 := by decide +kernel
private theorem ok662 : valid D 662 := by decide +kernel
private theorem ok663 : valid D 663 := by decide +kernel
private theorem ok664 : valid D 664 := by decide +kernel
private theorem ok665 : valid D 665 := by decide +kernel
private theorem ok666 : valid D 666 := by decide +kernel
private theorem ok667 : valid D 667 := by decide +kernel
private theorem ok668 : valid D 668 := by decide +kernel
private theorem ok669 : valid D 669 := by decide +kernel
private theorem ok670 : valid D 670 := by decide +kernel
private theorem ok671 : valid D 671 := by decide +kernel
theorem C640valid (i : Nat) (_lo : 640 ≤ i) (_hi : i < 672) : valid D i := by
  by_cases h640_672 : i < 656
  · by_cases h640_656 : i < 648
    · by_cases h640_648 : i < 644
      · by_cases h640_644 : i < 642
        · by_cases h640_642 : i < 641
          · have e : i = 640 := by omega
            subst i
            exact ok640
          · have e : i = 641 := by omega
            subst i
            exact ok641
        · by_cases h642_644 : i < 643
          · have e : i = 642 := by omega
            subst i
            exact ok642
          · have e : i = 643 := by omega
            subst i
            exact ok643
      · by_cases h644_648 : i < 646
        · by_cases h644_646 : i < 645
          · have e : i = 644 := by omega
            subst i
            exact ok644
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
    · by_cases h648_656 : i < 652
      · by_cases h648_652 : i < 650
        · by_cases h648_650 : i < 649
          · have e : i = 648 := by omega
            subst i
            exact ok648
          · have e : i = 649 := by omega
            subst i
            exact ok649
        · by_cases h650_652 : i < 651
          · have e : i = 650 := by omega
            subst i
            exact ok650
          · have e : i = 651 := by omega
            subst i
            exact ok651
      · by_cases h652_656 : i < 654
        · by_cases h652_654 : i < 653
          · have e : i = 652 := by omega
            subst i
            exact ok652
          · have e : i = 653 := by omega
            subst i
            exact ok653
        · by_cases h654_656 : i < 655
          · have e : i = 654 := by omega
            subst i
            exact ok654
          · have e : i = 655 := by omega
            subst i
            exact ok655
  · by_cases h656_672 : i < 664
    · by_cases h656_664 : i < 660
      · by_cases h656_660 : i < 658
        · by_cases h656_658 : i < 657
          · have e : i = 656 := by omega
            subst i
            exact ok656
          · have e : i = 657 := by omega
            subst i
            exact ok657
        · by_cases h658_660 : i < 659
          · have e : i = 658 := by omega
            subst i
            exact ok658
          · have e : i = 659 := by omega
            subst i
            exact ok659
      · by_cases h660_664 : i < 662
        · by_cases h660_662 : i < 661
          · have e : i = 660 := by omega
            subst i
            exact ok660
          · have e : i = 661 := by omega
            subst i
            exact ok661
        · by_cases h662_664 : i < 663
          · have e : i = 662 := by omega
            subst i
            exact ok662
          · have e : i = 663 := by omega
            subst i
            exact ok663
    · by_cases h664_672 : i < 668
      · by_cases h664_668 : i < 666
        · by_cases h664_666 : i < 665
          · have e : i = 664 := by omega
            subst i
            exact ok664
          · have e : i = 665 := by omega
            subst i
            exact ok665
        · by_cases h666_668 : i < 667
          · have e : i = 666 := by omega
            subst i
            exact ok666
          · have e : i = 667 := by omega
            subst i
            exact ok667
      · by_cases h668_672 : i < 670
        · by_cases h668_670 : i < 669
          · have e : i = 668 := by omega
            subst i
            exact ok668
          · have e : i = 669 := by omega
            subst i
            exact ok669
        · by_cases h670_672 : i < 671
          · have e : i = 670 := by omega
            subst i
            exact ok670
          · have e : i = 671 := by omega
            subst i
            exact ok671
end HaarMetaNineData
