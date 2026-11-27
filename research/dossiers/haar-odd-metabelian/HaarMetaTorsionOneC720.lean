import HaarMetaTorsionOneData
namespace HaarMetaTorsionOneData
open HaarMetaTorsionOneDAG HaarMetaTorsionOneVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
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
private theorem ok736 : valid D 736 := by decide +kernel
private theorem ok737 : valid D 737 := by decide +kernel
private theorem ok738 : valid D 738 := by decide +kernel
private theorem ok739 : valid D 739 := by decide +kernel
private theorem ok740 : valid D 740 := by decide +kernel
private theorem ok741 : valid D 741 := by decide +kernel
private theorem ok742 : valid D 742 := by decide +kernel
private theorem ok743 : valid D 743 := by decide +kernel
theorem C720valid (i : Nat) (_lo : 720 ≤ i) (_hi : i < 744) : valid D i := by
  by_cases h720_744 : i < 732
  · by_cases h720_732 : i < 726
    · by_cases h720_726 : i < 723
      · by_cases h720_723 : i < 721
        · have e : i = 720 := by omega
          subst i
          exact ok720
        · by_cases h721_723 : i < 722
          · have e : i = 721 := by omega
            subst i
            exact ok721
          · have e : i = 722 := by omega
            subst i
            exact ok722
      · by_cases h723_726 : i < 724
        · have e : i = 723 := by omega
          subst i
          exact ok723
        · by_cases h724_726 : i < 725
          · have e : i = 724 := by omega
            subst i
            exact ok724
          · have e : i = 725 := by omega
            subst i
            exact ok725
    · by_cases h726_732 : i < 729
      · by_cases h726_729 : i < 727
        · have e : i = 726 := by omega
          subst i
          exact ok726
        · by_cases h727_729 : i < 728
          · have e : i = 727 := by omega
            subst i
            exact ok727
          · have e : i = 728 := by omega
            subst i
            exact ok728
      · by_cases h729_732 : i < 730
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
  · by_cases h732_744 : i < 738
    · by_cases h732_738 : i < 735
      · by_cases h732_735 : i < 733
        · have e : i = 732 := by omega
          subst i
          exact ok732
        · by_cases h733_735 : i < 734
          · have e : i = 733 := by omega
            subst i
            exact ok733
          · have e : i = 734 := by omega
            subst i
            exact ok734
      · by_cases h735_738 : i < 736
        · have e : i = 735 := by omega
          subst i
          exact ok735
        · by_cases h736_738 : i < 737
          · have e : i = 736 := by omega
            subst i
            exact ok736
          · have e : i = 737 := by omega
            subst i
            exact ok737
    · by_cases h738_744 : i < 741
      · by_cases h738_741 : i < 739
        · have e : i = 738 := by omega
          subst i
          exact ok738
        · by_cases h739_741 : i < 740
          · have e : i = 739 := by omega
            subst i
            exact ok739
          · have e : i = 740 := by omega
            subst i
            exact ok740
      · by_cases h741_744 : i < 742
        · have e : i = 741 := by omega
          subst i
          exact ok741
        · by_cases h742_744 : i < 743
          · have e : i = 742 := by omega
            subst i
            exact ok742
          · have e : i = 743 := by omega
            subst i
            exact ok743
end HaarMetaTorsionOneData
