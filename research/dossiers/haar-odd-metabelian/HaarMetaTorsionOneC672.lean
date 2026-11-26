import HaarMetaTorsionOneData
namespace HaarMetaTorsionOneData
open HaarMetaTorsionOneDAG HaarMetaTorsionOneVoltage
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
theorem C672valid (i : Nat) (_lo : 672 ≤ i) (_hi : i < 696) : valid D i := by
  by_cases h672_696 : i < 684
  · by_cases h672_684 : i < 678
    · by_cases h672_678 : i < 675
      · by_cases h672_675 : i < 673
        · have e : i = 672 := by omega
          subst i
          exact ok672
        · by_cases h673_675 : i < 674
          · have e : i = 673 := by omega
            subst i
            exact ok673
          · have e : i = 674 := by omega
            subst i
            exact ok674
      · by_cases h675_678 : i < 676
        · have e : i = 675 := by omega
          subst i
          exact ok675
        · by_cases h676_678 : i < 677
          · have e : i = 676 := by omega
            subst i
            exact ok676
          · have e : i = 677 := by omega
            subst i
            exact ok677
    · by_cases h678_684 : i < 681
      · by_cases h678_681 : i < 679
        · have e : i = 678 := by omega
          subst i
          exact ok678
        · by_cases h679_681 : i < 680
          · have e : i = 679 := by omega
            subst i
            exact ok679
          · have e : i = 680 := by omega
            subst i
            exact ok680
      · by_cases h681_684 : i < 682
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
  · by_cases h684_696 : i < 690
    · by_cases h684_690 : i < 687
      · by_cases h684_687 : i < 685
        · have e : i = 684 := by omega
          subst i
          exact ok684
        · by_cases h685_687 : i < 686
          · have e : i = 685 := by omega
            subst i
            exact ok685
          · have e : i = 686 := by omega
            subst i
            exact ok686
      · by_cases h687_690 : i < 688
        · have e : i = 687 := by omega
          subst i
          exact ok687
        · by_cases h688_690 : i < 689
          · have e : i = 688 := by omega
            subst i
            exact ok688
          · have e : i = 689 := by omega
            subst i
            exact ok689
    · by_cases h690_696 : i < 693
      · by_cases h690_693 : i < 691
        · have e : i = 690 := by omega
          subst i
          exact ok690
        · by_cases h691_693 : i < 692
          · have e : i = 691 := by omega
            subst i
            exact ok691
          · have e : i = 692 := by omega
            subst i
            exact ok692
      · by_cases h693_696 : i < 694
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
end HaarMetaTorsionOneData
