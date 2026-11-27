import HaarMetaTorsionOneData
namespace HaarMetaTorsionOneData
open HaarMetaTorsionOneDAG HaarMetaTorsionOneVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
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
theorem C840valid (i : Nat) (_lo : 840 ≤ i) (_hi : i < 864) : valid D i := by
  by_cases h840_864 : i < 852
  · by_cases h840_852 : i < 846
    · by_cases h840_846 : i < 843
      · by_cases h840_843 : i < 841
        · have e : i = 840 := by omega
          subst i
          exact ok840
        · by_cases h841_843 : i < 842
          · have e : i = 841 := by omega
            subst i
            exact ok841
          · have e : i = 842 := by omega
            subst i
            exact ok842
      · by_cases h843_846 : i < 844
        · have e : i = 843 := by omega
          subst i
          exact ok843
        · by_cases h844_846 : i < 845
          · have e : i = 844 := by omega
            subst i
            exact ok844
          · have e : i = 845 := by omega
            subst i
            exact ok845
    · by_cases h846_852 : i < 849
      · by_cases h846_849 : i < 847
        · have e : i = 846 := by omega
          subst i
          exact ok846
        · by_cases h847_849 : i < 848
          · have e : i = 847 := by omega
            subst i
            exact ok847
          · have e : i = 848 := by omega
            subst i
            exact ok848
      · by_cases h849_852 : i < 850
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
  · by_cases h852_864 : i < 858
    · by_cases h852_858 : i < 855
      · by_cases h852_855 : i < 853
        · have e : i = 852 := by omega
          subst i
          exact ok852
        · by_cases h853_855 : i < 854
          · have e : i = 853 := by omega
            subst i
            exact ok853
          · have e : i = 854 := by omega
            subst i
            exact ok854
      · by_cases h855_858 : i < 856
        · have e : i = 855 := by omega
          subst i
          exact ok855
        · by_cases h856_858 : i < 857
          · have e : i = 856 := by omega
            subst i
            exact ok856
          · have e : i = 857 := by omega
            subst i
            exact ok857
    · by_cases h858_864 : i < 861
      · by_cases h858_861 : i < 859
        · have e : i = 858 := by omega
          subst i
          exact ok858
        · by_cases h859_861 : i < 860
          · have e : i = 859 := by omega
            subst i
            exact ok859
          · have e : i = 860 := by omega
            subst i
            exact ok860
      · by_cases h861_864 : i < 862
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
end HaarMetaTorsionOneData
