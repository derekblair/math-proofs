import HaarC5Data
namespace HaarC5Data
open HaarC5DAG HaarC5Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1152 : valid D 1152 := by decide +kernel
private theorem ok1153 : valid D 1153 := by decide +kernel
private theorem ok1154 : valid D 1154 := by decide +kernel
private theorem ok1155 : valid D 1155 := by decide +kernel
private theorem ok1156 : valid D 1156 := by decide +kernel
private theorem ok1157 : valid D 1157 := by decide +kernel
theorem C1152valid (i : Nat) (_lo : 1152 ≤ i) (_hi : i < 1158) : valid D i := by
  by_cases h1152_1158 : i < 1155
  · by_cases h1152_1155 : i < 1153
    · have e : i = 1152 := by omega
      subst i
      exact ok1152
    · by_cases h1153_1155 : i < 1154
      · have e : i = 1153 := by omega
        subst i
        exact ok1153
      · have e : i = 1154 := by omega
        subst i
        exact ok1154
  · by_cases h1155_1158 : i < 1156
    · have e : i = 1155 := by omega
      subst i
      exact ok1155
    · by_cases h1156_1158 : i < 1157
      · have e : i = 1156 := by omega
        subst i
        exact ok1156
      · have e : i = 1157 := by omega
        subst i
        exact ok1157
end HaarC5Data
