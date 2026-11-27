import HaarMetaS014Data
namespace HaarMetaS014Data
open HaarMetaS014DAG HaarMetaS014Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok96 : valid D 96 := by decide +kernel
private theorem ok97 : valid D 97 := by decide +kernel
private theorem ok98 : valid D 98 := by decide +kernel
private theorem ok99 : valid D 99 := by decide +kernel
private theorem ok100 : valid D 100 := by decide +kernel
private theorem ok101 : valid D 101 := by decide +kernel
private theorem ok102 : valid D 102 := by decide +kernel
private theorem ok103 : valid D 103 := by decide +kernel
private theorem ok104 : valid D 104 := by decide +kernel
private theorem ok105 : valid D 105 := by decide +kernel
private theorem ok106 : valid D 106 := by decide +kernel
private theorem ok107 : valid D 107 := by decide +kernel
private theorem ok108 : valid D 108 := by decide +kernel
private theorem ok109 : valid D 109 := by decide +kernel
private theorem ok110 : valid D 110 := by decide +kernel
private theorem ok111 : valid D 111 := by decide +kernel
private theorem ok112 : valid D 112 := by decide +kernel
private theorem ok113 : valid D 113 := by decide +kernel
private theorem ok114 : valid D 114 := by decide +kernel
private theorem ok115 : valid D 115 := by decide +kernel
private theorem ok116 : valid D 116 := by decide +kernel
private theorem ok117 : valid D 117 := by decide +kernel
private theorem ok118 : valid D 118 := by decide +kernel
private theorem ok119 : valid D 119 := by decide +kernel
theorem C096valid (i : Nat) (_lo : 96 ≤ i) (_hi : i < 120) : valid D i := by
  by_cases h96_120 : i < 108
  · by_cases h96_108 : i < 102
    · by_cases h96_102 : i < 99
      · by_cases h96_99 : i < 97
        · have e : i = 96 := by omega
          subst i
          exact ok96
        · by_cases h97_99 : i < 98
          · have e : i = 97 := by omega
            subst i
            exact ok97
          · have e : i = 98 := by omega
            subst i
            exact ok98
      · by_cases h99_102 : i < 100
        · have e : i = 99 := by omega
          subst i
          exact ok99
        · by_cases h100_102 : i < 101
          · have e : i = 100 := by omega
            subst i
            exact ok100
          · have e : i = 101 := by omega
            subst i
            exact ok101
    · by_cases h102_108 : i < 105
      · by_cases h102_105 : i < 103
        · have e : i = 102 := by omega
          subst i
          exact ok102
        · by_cases h103_105 : i < 104
          · have e : i = 103 := by omega
            subst i
            exact ok103
          · have e : i = 104 := by omega
            subst i
            exact ok104
      · by_cases h105_108 : i < 106
        · have e : i = 105 := by omega
          subst i
          exact ok105
        · by_cases h106_108 : i < 107
          · have e : i = 106 := by omega
            subst i
            exact ok106
          · have e : i = 107 := by omega
            subst i
            exact ok107
  · by_cases h108_120 : i < 114
    · by_cases h108_114 : i < 111
      · by_cases h108_111 : i < 109
        · have e : i = 108 := by omega
          subst i
          exact ok108
        · by_cases h109_111 : i < 110
          · have e : i = 109 := by omega
            subst i
            exact ok109
          · have e : i = 110 := by omega
            subst i
            exact ok110
      · by_cases h111_114 : i < 112
        · have e : i = 111 := by omega
          subst i
          exact ok111
        · by_cases h112_114 : i < 113
          · have e : i = 112 := by omega
            subst i
            exact ok112
          · have e : i = 113 := by omega
            subst i
            exact ok113
    · by_cases h114_120 : i < 117
      · by_cases h114_117 : i < 115
        · have e : i = 114 := by omega
          subst i
          exact ok114
        · by_cases h115_117 : i < 116
          · have e : i = 115 := by omega
            subst i
            exact ok115
          · have e : i = 116 := by omega
            subst i
            exact ok116
      · by_cases h117_120 : i < 118
        · have e : i = 117 := by omega
          subst i
          exact ok117
        · by_cases h118_120 : i < 119
          · have e : i = 118 := by omega
            subst i
            exact ok118
          · have e : i = 119 := by omega
            subst i
            exact ok119
end HaarMetaS014Data
