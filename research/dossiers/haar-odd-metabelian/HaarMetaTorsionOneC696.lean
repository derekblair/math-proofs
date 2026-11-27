import HaarMetaTorsionOneData
namespace HaarMetaTorsionOneData
open HaarMetaTorsionOneDAG HaarMetaTorsionOneVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok696 : valid D 696 := by decide +kernel
private theorem ok697 : valid D 697 := by decide +kernel
private theorem ok698 : valid D 698 := by decide +kernel
private theorem ok699 : valid D 699 := by decide +kernel
private theorem ok700 : valid D 700 := by decide +kernel
private theorem ok701 : valid D 701 := by decide +kernel
private theorem ok702 : valid D 702 := by decide +kernel
private theorem ok703 : valid D 703 := by decide +kernel
private theorem ok704 : valid D 704 := by decide +kernel
private theorem ok705 : valid D 705 := by decide +kernel
private theorem ok706 : valid D 706 := by decide +kernel
private theorem ok707 : valid D 707 := by decide +kernel
private theorem ok708 : valid D 708 := by decide +kernel
private theorem ok709 : valid D 709 := by decide +kernel
private theorem ok710 : valid D 710 := by decide +kernel
private theorem ok711 : valid D 711 := by decide +kernel
private theorem ok712 : valid D 712 := by decide +kernel
private theorem ok713 : valid D 713 := by decide +kernel
private theorem ok714 : valid D 714 := by decide +kernel
private theorem ok715 : valid D 715 := by decide +kernel
private theorem ok716 : valid D 716 := by decide +kernel
private theorem ok717 : valid D 717 := by decide +kernel
private theorem ok718 : valid D 718 := by decide +kernel
private theorem ok719 : valid D 719 := by decide +kernel
theorem C696valid (i : Nat) (_lo : 696 ≤ i) (_hi : i < 720) : valid D i := by
  by_cases h696_720 : i < 708
  · by_cases h696_708 : i < 702
    · by_cases h696_702 : i < 699
      · by_cases h696_699 : i < 697
        · have e : i = 696 := by omega
          subst i
          exact ok696
        · by_cases h697_699 : i < 698
          · have e : i = 697 := by omega
            subst i
            exact ok697
          · have e : i = 698 := by omega
            subst i
            exact ok698
      · by_cases h699_702 : i < 700
        · have e : i = 699 := by omega
          subst i
          exact ok699
        · by_cases h700_702 : i < 701
          · have e : i = 700 := by omega
            subst i
            exact ok700
          · have e : i = 701 := by omega
            subst i
            exact ok701
    · by_cases h702_708 : i < 705
      · by_cases h702_705 : i < 703
        · have e : i = 702 := by omega
          subst i
          exact ok702
        · by_cases h703_705 : i < 704
          · have e : i = 703 := by omega
            subst i
            exact ok703
          · have e : i = 704 := by omega
            subst i
            exact ok704
      · by_cases h705_708 : i < 706
        · have e : i = 705 := by omega
          subst i
          exact ok705
        · by_cases h706_708 : i < 707
          · have e : i = 706 := by omega
            subst i
            exact ok706
          · have e : i = 707 := by omega
            subst i
            exact ok707
  · by_cases h708_720 : i < 714
    · by_cases h708_714 : i < 711
      · by_cases h708_711 : i < 709
        · have e : i = 708 := by omega
          subst i
          exact ok708
        · by_cases h709_711 : i < 710
          · have e : i = 709 := by omega
            subst i
            exact ok709
          · have e : i = 710 := by omega
            subst i
            exact ok710
      · by_cases h711_714 : i < 712
        · have e : i = 711 := by omega
          subst i
          exact ok711
        · by_cases h712_714 : i < 713
          · have e : i = 712 := by omega
            subst i
            exact ok712
          · have e : i = 713 := by omega
            subst i
            exact ok713
    · by_cases h714_720 : i < 717
      · by_cases h714_717 : i < 715
        · have e : i = 714 := by omega
          subst i
          exact ok714
        · by_cases h715_717 : i < 716
          · have e : i = 715 := by omega
            subst i
            exact ok715
          · have e : i = 716 := by omega
            subst i
            exact ok716
      · by_cases h717_720 : i < 718
        · have e : i = 717 := by omega
          subst i
          exact ok717
        · by_cases h718_720 : i < 719
          · have e : i = 718 := by omega
            subst i
            exact ok718
          · have e : i = 719 := by omega
            subst i
            exact ok719
end HaarMetaTorsionOneData
