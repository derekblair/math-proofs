import HaarMetaNineData
namespace HaarMetaNineData
open HaarMetaNineDAG HaarMetaNineVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok832 : valid D 832 := by decide +kernel
private theorem ok833 : valid D 833 := by decide +kernel
private theorem ok834 : valid D 834 := by decide +kernel
private theorem ok835 : valid D 835 := by decide +kernel
private theorem ok836 : valid D 836 := by decide +kernel
private theorem ok837 : valid D 837 := by decide +kernel
private theorem ok838 : valid D 838 := by decide +kernel
private theorem ok839 : valid D 839 := by decide +kernel
private theorem ok840 : valid D 840 := by decide +kernel
private theorem ok841 : valid D 841 := by decide +kernel
private theorem ok842 : valid D 842 := by decide +kernel
private theorem ok843 : valid D 843 := by decide +kernel
private theorem ok844 : valid D 844 := by decide +kernel
private theorem ok845 : valid D 845 := by decide +kernel
private theorem ok846 : valid D 846 := by decide +kernel
private theorem ok847 : valid D 847 := by decide +kernel
private theorem ok848 : valid D 848 := by decide +kernel
private theorem ok849 : valid D 849 := by decide +kernel
private theorem ok850 : valid D 850 := by decide +kernel
private theorem ok851 : valid D 851 := by decide +kernel
private theorem ok852 : valid D 852 := by decide +kernel
private theorem ok853 : valid D 853 := by decide +kernel
private theorem ok854 : valid D 854 := by decide +kernel
private theorem ok855 : valid D 855 := by decide +kernel
private theorem ok856 : valid D 856 := by decide +kernel
private theorem ok857 : valid D 857 := by decide +kernel
private theorem ok858 : valid D 858 := by decide +kernel
private theorem ok859 : valid D 859 := by decide +kernel
private theorem ok860 : valid D 860 := by decide +kernel
private theorem ok861 : valid D 861 := by decide +kernel
private theorem ok862 : valid D 862 := by decide +kernel
private theorem ok863 : valid D 863 := by decide +kernel
theorem C832valid (i : Nat) (_lo : 832 ≤ i) (_hi : i < 864) : valid D i := by
  by_cases h832_864 : i < 848
  · by_cases h832_848 : i < 840
    · by_cases h832_840 : i < 836
      · by_cases h832_836 : i < 834
        · by_cases h832_834 : i < 833
          · have e : i = 832 := by omega
            subst i
            exact ok832
          · have e : i = 833 := by omega
            subst i
            exact ok833
        · by_cases h834_836 : i < 835
          · have e : i = 834 := by omega
            subst i
            exact ok834
          · have e : i = 835 := by omega
            subst i
            exact ok835
      · by_cases h836_840 : i < 838
        · by_cases h836_838 : i < 837
          · have e : i = 836 := by omega
            subst i
            exact ok836
          · have e : i = 837 := by omega
            subst i
            exact ok837
        · by_cases h838_840 : i < 839
          · have e : i = 838 := by omega
            subst i
            exact ok838
          · have e : i = 839 := by omega
            subst i
            exact ok839
    · by_cases h840_848 : i < 844
      · by_cases h840_844 : i < 842
        · by_cases h840_842 : i < 841
          · have e : i = 840 := by omega
            subst i
            exact ok840
          · have e : i = 841 := by omega
            subst i
            exact ok841
        · by_cases h842_844 : i < 843
          · have e : i = 842 := by omega
            subst i
            exact ok842
          · have e : i = 843 := by omega
            subst i
            exact ok843
      · by_cases h844_848 : i < 846
        · by_cases h844_846 : i < 845
          · have e : i = 844 := by omega
            subst i
            exact ok844
          · have e : i = 845 := by omega
            subst i
            exact ok845
        · by_cases h846_848 : i < 847
          · have e : i = 846 := by omega
            subst i
            exact ok846
          · have e : i = 847 := by omega
            subst i
            exact ok847
  · by_cases h848_864 : i < 856
    · by_cases h848_856 : i < 852
      · by_cases h848_852 : i < 850
        · by_cases h848_850 : i < 849
          · have e : i = 848 := by omega
            subst i
            exact ok848
          · have e : i = 849 := by omega
            subst i
            exact ok849
        · by_cases h850_852 : i < 851
          · have e : i = 850 := by omega
            subst i
            exact ok850
          · have e : i = 851 := by omega
            subst i
            exact ok851
      · by_cases h852_856 : i < 854
        · by_cases h852_854 : i < 853
          · have e : i = 852 := by omega
            subst i
            exact ok852
          · have e : i = 853 := by omega
            subst i
            exact ok853
        · by_cases h854_856 : i < 855
          · have e : i = 854 := by omega
            subst i
            exact ok854
          · have e : i = 855 := by omega
            subst i
            exact ok855
    · by_cases h856_864 : i < 860
      · by_cases h856_860 : i < 858
        · by_cases h856_858 : i < 857
          · have e : i = 856 := by omega
            subst i
            exact ok856
          · have e : i = 857 := by omega
            subst i
            exact ok857
        · by_cases h858_860 : i < 859
          · have e : i = 858 := by omega
            subst i
            exact ok858
          · have e : i = 859 := by omega
            subst i
            exact ok859
      · by_cases h860_864 : i < 862
        · by_cases h860_862 : i < 861
          · have e : i = 860 := by omega
            subst i
            exact ok860
          · have e : i = 861 := by omega
            subst i
            exact ok861
        · by_cases h862_864 : i < 863
          · have e : i = 862 := by omega
            subst i
            exact ok862
          · have e : i = 863 := by omega
            subst i
            exact ok863
end HaarMetaNineData
