import HaarK33Data
namespace HaarK33Data
open HaarK33DAG HaarK33Voltage
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
theorem C096valid (i : Nat) (_lo : 96 ≤ i) (_hi : i < 112) : valid D i := by
  by_cases h96_112 : i < 104
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
end HaarK33Data
