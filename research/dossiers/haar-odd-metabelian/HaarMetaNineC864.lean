import HaarMetaNineData
namespace HaarMetaNineData
open HaarMetaNineDAG HaarMetaNineVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok864 : valid D 864 := by decide +kernel
private theorem ok865 : valid D 865 := by decide +kernel
private theorem ok866 : valid D 866 := by decide +kernel
private theorem ok867 : valid D 867 := by decide +kernel
private theorem ok868 : valid D 868 := by decide +kernel
private theorem ok869 : valid D 869 := by decide +kernel
private theorem ok870 : valid D 870 := by decide +kernel
private theorem ok871 : valid D 871 := by decide +kernel
private theorem ok872 : valid D 872 := by decide +kernel
private theorem ok873 : valid D 873 := by decide +kernel
private theorem ok874 : valid D 874 := by decide +kernel
private theorem ok875 : valid D 875 := by decide +kernel
private theorem ok876 : valid D 876 := by decide +kernel
private theorem ok877 : valid D 877 := by decide +kernel
private theorem ok878 : valid D 878 := by decide +kernel
private theorem ok879 : valid D 879 := by decide +kernel
private theorem ok880 : valid D 880 := by decide +kernel
private theorem ok881 : valid D 881 := by decide +kernel
private theorem ok882 : valid D 882 := by decide +kernel
private theorem ok883 : valid D 883 := by decide +kernel
private theorem ok884 : valid D 884 := by decide +kernel
private theorem ok885 : valid D 885 := by decide +kernel
private theorem ok886 : valid D 886 := by decide +kernel
private theorem ok887 : valid D 887 := by decide +kernel
private theorem ok888 : valid D 888 := by decide +kernel
private theorem ok889 : valid D 889 := by decide +kernel
private theorem ok890 : valid D 890 := by decide +kernel
private theorem ok891 : valid D 891 := by decide +kernel
private theorem ok892 : valid D 892 := by decide +kernel
private theorem ok893 : valid D 893 := by decide +kernel
private theorem ok894 : valid D 894 := by decide +kernel
private theorem ok895 : valid D 895 := by decide +kernel
theorem C864valid (i : Nat) (_lo : 864 ≤ i) (_hi : i < 896) : valid D i := by
  by_cases h864_896 : i < 880
  · by_cases h864_880 : i < 872
    · by_cases h864_872 : i < 868
      · by_cases h864_868 : i < 866
        · by_cases h864_866 : i < 865
          · have e : i = 864 := by omega
            subst i
            exact ok864
          · have e : i = 865 := by omega
            subst i
            exact ok865
        · by_cases h866_868 : i < 867
          · have e : i = 866 := by omega
            subst i
            exact ok866
          · have e : i = 867 := by omega
            subst i
            exact ok867
      · by_cases h868_872 : i < 870
        · by_cases h868_870 : i < 869
          · have e : i = 868 := by omega
            subst i
            exact ok868
          · have e : i = 869 := by omega
            subst i
            exact ok869
        · by_cases h870_872 : i < 871
          · have e : i = 870 := by omega
            subst i
            exact ok870
          · have e : i = 871 := by omega
            subst i
            exact ok871
    · by_cases h872_880 : i < 876
      · by_cases h872_876 : i < 874
        · by_cases h872_874 : i < 873
          · have e : i = 872 := by omega
            subst i
            exact ok872
          · have e : i = 873 := by omega
            subst i
            exact ok873
        · by_cases h874_876 : i < 875
          · have e : i = 874 := by omega
            subst i
            exact ok874
          · have e : i = 875 := by omega
            subst i
            exact ok875
      · by_cases h876_880 : i < 878
        · by_cases h876_878 : i < 877
          · have e : i = 876 := by omega
            subst i
            exact ok876
          · have e : i = 877 := by omega
            subst i
            exact ok877
        · by_cases h878_880 : i < 879
          · have e : i = 878 := by omega
            subst i
            exact ok878
          · have e : i = 879 := by omega
            subst i
            exact ok879
  · by_cases h880_896 : i < 888
    · by_cases h880_888 : i < 884
      · by_cases h880_884 : i < 882
        · by_cases h880_882 : i < 881
          · have e : i = 880 := by omega
            subst i
            exact ok880
          · have e : i = 881 := by omega
            subst i
            exact ok881
        · by_cases h882_884 : i < 883
          · have e : i = 882 := by omega
            subst i
            exact ok882
          · have e : i = 883 := by omega
            subst i
            exact ok883
      · by_cases h884_888 : i < 886
        · by_cases h884_886 : i < 885
          · have e : i = 884 := by omega
            subst i
            exact ok884
          · have e : i = 885 := by omega
            subst i
            exact ok885
        · by_cases h886_888 : i < 887
          · have e : i = 886 := by omega
            subst i
            exact ok886
          · have e : i = 887 := by omega
            subst i
            exact ok887
    · by_cases h888_896 : i < 892
      · by_cases h888_892 : i < 890
        · by_cases h888_890 : i < 889
          · have e : i = 888 := by omega
            subst i
            exact ok888
          · have e : i = 889 := by omega
            subst i
            exact ok889
        · by_cases h890_892 : i < 891
          · have e : i = 890 := by omega
            subst i
            exact ok890
          · have e : i = 891 := by omega
            subst i
            exact ok891
      · by_cases h892_896 : i < 894
        · by_cases h892_894 : i < 893
          · have e : i = 892 := by omega
            subst i
            exact ok892
          · have e : i = 893 := by omega
            subst i
            exact ok893
        · by_cases h894_896 : i < 895
          · have e : i = 894 := by omega
            subst i
            exact ok894
          · have e : i = 895 := by omega
            subst i
            exact ok895
end HaarMetaNineData
