import HaarC5Data
namespace HaarC5Data
open HaarC5DAG HaarC5Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok744 : valid D 744 := by decide +kernel
private theorem ok745 : valid D 745 := by decide +kernel
private theorem ok746 : valid D 746 := by decide +kernel
private theorem ok747 : valid D 747 := by decide +kernel
private theorem ok748 : valid D 748 := by decide +kernel
private theorem ok749 : valid D 749 := by decide +kernel
private theorem ok750 : valid D 750 := by decide +kernel
private theorem ok751 : valid D 751 := by decide +kernel
private theorem ok752 : valid D 752 := by decide +kernel
private theorem ok753 : valid D 753 := by decide +kernel
private theorem ok754 : valid D 754 := by decide +kernel
private theorem ok755 : valid D 755 := by decide +kernel
private theorem ok756 : valid D 756 := by decide +kernel
private theorem ok757 : valid D 757 := by decide +kernel
private theorem ok758 : valid D 758 := by decide +kernel
private theorem ok759 : valid D 759 := by decide +kernel
private theorem ok760 : valid D 760 := by decide +kernel
private theorem ok761 : valid D 761 := by decide +kernel
private theorem ok762 : valid D 762 := by decide +kernel
private theorem ok763 : valid D 763 := by decide +kernel
private theorem ok764 : valid D 764 := by decide +kernel
private theorem ok765 : valid D 765 := by decide +kernel
private theorem ok766 : valid D 766 := by decide +kernel
private theorem ok767 : valid D 767 := by decide +kernel
theorem C744valid (i : Nat) (_lo : 744 ≤ i) (_hi : i < 768) : valid D i := by
  by_cases h744_768 : i < 756
  · by_cases h744_756 : i < 750
    · by_cases h744_750 : i < 747
      · by_cases h744_747 : i < 745
        · have e : i = 744 := by omega
          subst i
          exact ok744
        · by_cases h745_747 : i < 746
          · have e : i = 745 := by omega
            subst i
            exact ok745
          · have e : i = 746 := by omega
            subst i
            exact ok746
      · by_cases h747_750 : i < 748
        · have e : i = 747 := by omega
          subst i
          exact ok747
        · by_cases h748_750 : i < 749
          · have e : i = 748 := by omega
            subst i
            exact ok748
          · have e : i = 749 := by omega
            subst i
            exact ok749
    · by_cases h750_756 : i < 753
      · by_cases h750_753 : i < 751
        · have e : i = 750 := by omega
          subst i
          exact ok750
        · by_cases h751_753 : i < 752
          · have e : i = 751 := by omega
            subst i
            exact ok751
          · have e : i = 752 := by omega
            subst i
            exact ok752
      · by_cases h753_756 : i < 754
        · have e : i = 753 := by omega
          subst i
          exact ok753
        · by_cases h754_756 : i < 755
          · have e : i = 754 := by omega
            subst i
            exact ok754
          · have e : i = 755 := by omega
            subst i
            exact ok755
  · by_cases h756_768 : i < 762
    · by_cases h756_762 : i < 759
      · by_cases h756_759 : i < 757
        · have e : i = 756 := by omega
          subst i
          exact ok756
        · by_cases h757_759 : i < 758
          · have e : i = 757 := by omega
            subst i
            exact ok757
          · have e : i = 758 := by omega
            subst i
            exact ok758
      · by_cases h759_762 : i < 760
        · have e : i = 759 := by omega
          subst i
          exact ok759
        · by_cases h760_762 : i < 761
          · have e : i = 760 := by omega
            subst i
            exact ok760
          · have e : i = 761 := by omega
            subst i
            exact ok761
    · by_cases h762_768 : i < 765
      · by_cases h762_765 : i < 763
        · have e : i = 762 := by omega
          subst i
          exact ok762
        · by_cases h763_765 : i < 764
          · have e : i = 763 := by omega
            subst i
            exact ok763
          · have e : i = 764 := by omega
            subst i
            exact ok764
      · by_cases h765_768 : i < 766
        · have e : i = 765 := by omega
          subst i
          exact ok765
        · by_cases h766_768 : i < 767
          · have e : i = 766 := by omega
            subst i
            exact ok766
          · have e : i = 767 := by omega
            subst i
            exact ok767
end HaarC5Data
