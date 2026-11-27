import HaarMetaNineData
namespace HaarMetaNineData
open HaarMetaNineDAG HaarMetaNineVoltage
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
private theorem ok120 : valid D 120 := by decide +kernel
private theorem ok121 : valid D 121 := by decide +kernel
private theorem ok122 : valid D 122 := by decide +kernel
private theorem ok123 : valid D 123 := by decide +kernel
private theorem ok124 : valid D 124 := by decide +kernel
private theorem ok125 : valid D 125 := by decide +kernel
private theorem ok126 : valid D 126 := by decide +kernel
private theorem ok127 : valid D 127 := by decide +kernel
theorem C096valid (i : Nat) (_lo : 96 ≤ i) (_hi : i < 128) : valid D i := by
  by_cases h96_128 : i < 112
  · by_cases h96_112 : i < 104
    · by_cases h96_104 : i < 100
      · by_cases h96_100 : i < 98
        · by_cases h96_98 : i < 97
          · have e : i = 96 := by omega
            subst i
            exact ok96
          · have e : i = 97 := by omega
            subst i
            exact ok97
        · by_cases h98_100 : i < 99
          · have e : i = 98 := by omega
            subst i
            exact ok98
          · have e : i = 99 := by omega
            subst i
            exact ok99
      · by_cases h100_104 : i < 102
        · by_cases h100_102 : i < 101
          · have e : i = 100 := by omega
            subst i
            exact ok100
          · have e : i = 101 := by omega
            subst i
            exact ok101
        · by_cases h102_104 : i < 103
          · have e : i = 102 := by omega
            subst i
            exact ok102
          · have e : i = 103 := by omega
            subst i
            exact ok103
    · by_cases h104_112 : i < 108
      · by_cases h104_108 : i < 106
        · by_cases h104_106 : i < 105
          · have e : i = 104 := by omega
            subst i
            exact ok104
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
      · by_cases h108_112 : i < 110
        · by_cases h108_110 : i < 109
          · have e : i = 108 := by omega
            subst i
            exact ok108
          · have e : i = 109 := by omega
            subst i
            exact ok109
        · by_cases h110_112 : i < 111
          · have e : i = 110 := by omega
            subst i
            exact ok110
          · have e : i = 111 := by omega
            subst i
            exact ok111
  · by_cases h112_128 : i < 120
    · by_cases h112_120 : i < 116
      · by_cases h112_116 : i < 114
        · by_cases h112_114 : i < 113
          · have e : i = 112 := by omega
            subst i
            exact ok112
          · have e : i = 113 := by omega
            subst i
            exact ok113
        · by_cases h114_116 : i < 115
          · have e : i = 114 := by omega
            subst i
            exact ok114
          · have e : i = 115 := by omega
            subst i
            exact ok115
      · by_cases h116_120 : i < 118
        · by_cases h116_118 : i < 117
          · have e : i = 116 := by omega
            subst i
            exact ok116
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
    · by_cases h120_128 : i < 124
      · by_cases h120_124 : i < 122
        · by_cases h120_122 : i < 121
          · have e : i = 120 := by omega
            subst i
            exact ok120
          · have e : i = 121 := by omega
            subst i
            exact ok121
        · by_cases h122_124 : i < 123
          · have e : i = 122 := by omega
            subst i
            exact ok122
          · have e : i = 123 := by omega
            subst i
            exact ok123
      · by_cases h124_128 : i < 126
        · by_cases h124_126 : i < 125
          · have e : i = 124 := by omega
            subst i
            exact ok124
          · have e : i = 125 := by omega
            subst i
            exact ok125
        · by_cases h126_128 : i < 127
          · have e : i = 126 := by omega
            subst i
            exact ok126
          · have e : i = 127 := by omega
            subst i
            exact ok127
end HaarMetaNineData
