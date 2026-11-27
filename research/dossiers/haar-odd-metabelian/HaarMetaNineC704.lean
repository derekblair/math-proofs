import HaarMetaNineData
namespace HaarMetaNineData
open HaarMetaNineDAG HaarMetaNineVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
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
private theorem ok720 : valid D 720 := by decide +kernel
private theorem ok721 : valid D 721 := by decide +kernel
private theorem ok722 : valid D 722 := by decide +kernel
private theorem ok723 : valid D 723 := by decide +kernel
private theorem ok724 : valid D 724 := by decide +kernel
private theorem ok725 : valid D 725 := by decide +kernel
private theorem ok726 : valid D 726 := by decide +kernel
private theorem ok727 : valid D 727 := by decide +kernel
private theorem ok728 : valid D 728 := by decide +kernel
private theorem ok729 : valid D 729 := by decide +kernel
private theorem ok730 : valid D 730 := by decide +kernel
private theorem ok731 : valid D 731 := by decide +kernel
private theorem ok732 : valid D 732 := by decide +kernel
private theorem ok733 : valid D 733 := by decide +kernel
private theorem ok734 : valid D 734 := by decide +kernel
private theorem ok735 : valid D 735 := by decide +kernel
theorem C704valid (i : Nat) (_lo : 704 ≤ i) (_hi : i < 736) : valid D i := by
  by_cases h704_736 : i < 720
  · by_cases h704_720 : i < 712
    · by_cases h704_712 : i < 708
      · by_cases h704_708 : i < 706
        · by_cases h704_706 : i < 705
          · have e : i = 704 := by omega
            subst i
            exact ok704
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
      · by_cases h708_712 : i < 710
        · by_cases h708_710 : i < 709
          · have e : i = 708 := by omega
            subst i
            exact ok708
          · have e : i = 709 := by omega
            subst i
            exact ok709
        · by_cases h710_712 : i < 711
          · have e : i = 710 := by omega
            subst i
            exact ok710
          · have e : i = 711 := by omega
            subst i
            exact ok711
    · by_cases h712_720 : i < 716
      · by_cases h712_716 : i < 714
        · by_cases h712_714 : i < 713
          · have e : i = 712 := by omega
            subst i
            exact ok712
          · have e : i = 713 := by omega
            subst i
            exact ok713
        · by_cases h714_716 : i < 715
          · have e : i = 714 := by omega
            subst i
            exact ok714
          · have e : i = 715 := by omega
            subst i
            exact ok715
      · by_cases h716_720 : i < 718
        · by_cases h716_718 : i < 717
          · have e : i = 716 := by omega
            subst i
            exact ok716
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
  · by_cases h720_736 : i < 728
    · by_cases h720_728 : i < 724
      · by_cases h720_724 : i < 722
        · by_cases h720_722 : i < 721
          · have e : i = 720 := by omega
            subst i
            exact ok720
          · have e : i = 721 := by omega
            subst i
            exact ok721
        · by_cases h722_724 : i < 723
          · have e : i = 722 := by omega
            subst i
            exact ok722
          · have e : i = 723 := by omega
            subst i
            exact ok723
      · by_cases h724_728 : i < 726
        · by_cases h724_726 : i < 725
          · have e : i = 724 := by omega
            subst i
            exact ok724
          · have e : i = 725 := by omega
            subst i
            exact ok725
        · by_cases h726_728 : i < 727
          · have e : i = 726 := by omega
            subst i
            exact ok726
          · have e : i = 727 := by omega
            subst i
            exact ok727
    · by_cases h728_736 : i < 732
      · by_cases h728_732 : i < 730
        · by_cases h728_730 : i < 729
          · have e : i = 728 := by omega
            subst i
            exact ok728
          · have e : i = 729 := by omega
            subst i
            exact ok729
        · by_cases h730_732 : i < 731
          · have e : i = 730 := by omega
            subst i
            exact ok730
          · have e : i = 731 := by omega
            subst i
            exact ok731
      · by_cases h732_736 : i < 734
        · by_cases h732_734 : i < 733
          · have e : i = 732 := by omega
            subst i
            exact ok732
          · have e : i = 733 := by omega
            subst i
            exact ok733
        · by_cases h734_736 : i < 735
          · have e : i = 734 := by omega
            subst i
            exact ok734
          · have e : i = 735 := by omega
            subst i
            exact ok735
end HaarMetaNineData
