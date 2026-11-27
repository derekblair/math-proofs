import HaarMetaTorsionOneData
namespace HaarMetaTorsionOneData
open HaarMetaTorsionOneDAG HaarMetaTorsionOneVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
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
theorem C648valid (i : Nat) (_lo : 648 ≤ i) (_hi : i < 672) : valid D i := by
  by_cases h648_672 : i < 660
  · by_cases h648_660 : i < 654
    · by_cases h648_654 : i < 651
      · by_cases h648_651 : i < 649
        · have e : i = 648 := by omega
          subst i
          exact ok648
        · by_cases h649_651 : i < 650
          · have e : i = 649 := by omega
            subst i
            exact ok649
          · have e : i = 650 := by omega
            subst i
            exact ok650
      · by_cases h651_654 : i < 652
        · have e : i = 651 := by omega
          subst i
          exact ok651
        · by_cases h652_654 : i < 653
          · have e : i = 652 := by omega
            subst i
            exact ok652
          · have e : i = 653 := by omega
            subst i
            exact ok653
    · by_cases h654_660 : i < 657
      · by_cases h654_657 : i < 655
        · have e : i = 654 := by omega
          subst i
          exact ok654
        · by_cases h655_657 : i < 656
          · have e : i = 655 := by omega
            subst i
            exact ok655
          · have e : i = 656 := by omega
            subst i
            exact ok656
      · by_cases h657_660 : i < 658
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
  · by_cases h660_672 : i < 666
    · by_cases h660_666 : i < 663
      · by_cases h660_663 : i < 661
        · have e : i = 660 := by omega
          subst i
          exact ok660
        · by_cases h661_663 : i < 662
          · have e : i = 661 := by omega
            subst i
            exact ok661
          · have e : i = 662 := by omega
            subst i
            exact ok662
      · by_cases h663_666 : i < 664
        · have e : i = 663 := by omega
          subst i
          exact ok663
        · by_cases h664_666 : i < 665
          · have e : i = 664 := by omega
            subst i
            exact ok664
          · have e : i = 665 := by omega
            subst i
            exact ok665
    · by_cases h666_672 : i < 669
      · by_cases h666_669 : i < 667
        · have e : i = 666 := by omega
          subst i
          exact ok666
        · by_cases h667_669 : i < 668
          · have e : i = 667 := by omega
            subst i
            exact ok667
          · have e : i = 668 := by omega
            subst i
            exact ok668
      · by_cases h669_672 : i < 670
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
end HaarMetaTorsionOneData
