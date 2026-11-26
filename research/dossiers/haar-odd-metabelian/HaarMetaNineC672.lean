import HaarMetaNineData
namespace HaarMetaNineData
open HaarMetaNineDAG HaarMetaNineVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok672 : valid D 672 := by decide +kernel
private theorem ok673 : valid D 673 := by decide +kernel
private theorem ok674 : valid D 674 := by decide +kernel
private theorem ok675 : valid D 675 := by decide +kernel
private theorem ok676 : valid D 676 := by decide +kernel
private theorem ok677 : valid D 677 := by decide +kernel
private theorem ok678 : valid D 678 := by decide +kernel
private theorem ok679 : valid D 679 := by decide +kernel
private theorem ok680 : valid D 680 := by decide +kernel
private theorem ok681 : valid D 681 := by decide +kernel
private theorem ok682 : valid D 682 := by decide +kernel
private theorem ok683 : valid D 683 := by decide +kernel
private theorem ok684 : valid D 684 := by decide +kernel
private theorem ok685 : valid D 685 := by decide +kernel
private theorem ok686 : valid D 686 := by decide +kernel
private theorem ok687 : valid D 687 := by decide +kernel
private theorem ok688 : valid D 688 := by decide +kernel
private theorem ok689 : valid D 689 := by decide +kernel
private theorem ok690 : valid D 690 := by decide +kernel
private theorem ok691 : valid D 691 := by decide +kernel
private theorem ok692 : valid D 692 := by decide +kernel
private theorem ok693 : valid D 693 := by decide +kernel
private theorem ok694 : valid D 694 := by decide +kernel
private theorem ok695 : valid D 695 := by decide +kernel
private theorem ok696 : valid D 696 := by decide +kernel
private theorem ok697 : valid D 697 := by decide +kernel
private theorem ok698 : valid D 698 := by decide +kernel
private theorem ok699 : valid D 699 := by decide +kernel
private theorem ok700 : valid D 700 := by decide +kernel
private theorem ok701 : valid D 701 := by decide +kernel
private theorem ok702 : valid D 702 := by decide +kernel
private theorem ok703 : valid D 703 := by decide +kernel
theorem C672valid (i : Nat) (_lo : 672 ≤ i) (_hi : i < 704) : valid D i := by
  by_cases h672_704 : i < 688
  · by_cases h672_688 : i < 680
    · by_cases h672_680 : i < 676
      · by_cases h672_676 : i < 674
        · by_cases h672_674 : i < 673
          · have e : i = 672 := by omega
            subst i
            exact ok672
          · have e : i = 673 := by omega
            subst i
            exact ok673
        · by_cases h674_676 : i < 675
          · have e : i = 674 := by omega
            subst i
            exact ok674
          · have e : i = 675 := by omega
            subst i
            exact ok675
      · by_cases h676_680 : i < 678
        · by_cases h676_678 : i < 677
          · have e : i = 676 := by omega
            subst i
            exact ok676
          · have e : i = 677 := by omega
            subst i
            exact ok677
        · by_cases h678_680 : i < 679
          · have e : i = 678 := by omega
            subst i
            exact ok678
          · have e : i = 679 := by omega
            subst i
            exact ok679
    · by_cases h680_688 : i < 684
      · by_cases h680_684 : i < 682
        · by_cases h680_682 : i < 681
          · have e : i = 680 := by omega
            subst i
            exact ok680
          · have e : i = 681 := by omega
            subst i
            exact ok681
        · by_cases h682_684 : i < 683
          · have e : i = 682 := by omega
            subst i
            exact ok682
          · have e : i = 683 := by omega
            subst i
            exact ok683
      · by_cases h684_688 : i < 686
        · by_cases h684_686 : i < 685
          · have e : i = 684 := by omega
            subst i
            exact ok684
          · have e : i = 685 := by omega
            subst i
            exact ok685
        · by_cases h686_688 : i < 687
          · have e : i = 686 := by omega
            subst i
            exact ok686
          · have e : i = 687 := by omega
            subst i
            exact ok687
  · by_cases h688_704 : i < 696
    · by_cases h688_696 : i < 692
      · by_cases h688_692 : i < 690
        · by_cases h688_690 : i < 689
          · have e : i = 688 := by omega
            subst i
            exact ok688
          · have e : i = 689 := by omega
            subst i
            exact ok689
        · by_cases h690_692 : i < 691
          · have e : i = 690 := by omega
            subst i
            exact ok690
          · have e : i = 691 := by omega
            subst i
            exact ok691
      · by_cases h692_696 : i < 694
        · by_cases h692_694 : i < 693
          · have e : i = 692 := by omega
            subst i
            exact ok692
          · have e : i = 693 := by omega
            subst i
            exact ok693
        · by_cases h694_696 : i < 695
          · have e : i = 694 := by omega
            subst i
            exact ok694
          · have e : i = 695 := by omega
            subst i
            exact ok695
    · by_cases h696_704 : i < 700
      · by_cases h696_700 : i < 698
        · by_cases h696_698 : i < 697
          · have e : i = 696 := by omega
            subst i
            exact ok696
          · have e : i = 697 := by omega
            subst i
            exact ok697
        · by_cases h698_700 : i < 699
          · have e : i = 698 := by omega
            subst i
            exact ok698
          · have e : i = 699 := by omega
            subst i
            exact ok699
      · by_cases h700_704 : i < 702
        · by_cases h700_702 : i < 701
          · have e : i = 700 := by omega
            subst i
            exact ok700
          · have e : i = 701 := by omega
            subst i
            exact ok701
        · by_cases h702_704 : i < 703
          · have e : i = 702 := by omega
            subst i
            exact ok702
          · have e : i = 703 := by omega
            subst i
            exact ok703
end HaarMetaNineData
