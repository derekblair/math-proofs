import HaarK33Data
namespace HaarK33Data
open HaarK33DAG HaarK33Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok160 : valid D 160 := by decide +kernel
private theorem ok161 : valid D 161 := by decide +kernel
private theorem ok162 : valid D 162 := by decide +kernel
private theorem ok163 : valid D 163 := by decide +kernel
private theorem ok164 : valid D 164 := by decide +kernel
private theorem ok165 : valid D 165 := by decide +kernel
private theorem ok166 : valid D 166 := by decide +kernel
private theorem ok167 : valid D 167 := by decide +kernel
private theorem ok168 : valid D 168 := by decide +kernel
private theorem ok169 : valid D 169 := by decide +kernel
private theorem ok170 : valid D 170 := by decide +kernel
private theorem ok171 : valid D 171 := by decide +kernel
private theorem ok172 : valid D 172 := by decide +kernel
private theorem ok173 : valid D 173 := by decide +kernel
private theorem ok174 : valid D 174 := by decide +kernel
private theorem ok175 : valid D 175 := by decide +kernel
theorem C160valid (i : Nat) (_lo : 160 ≤ i) (_hi : i < 176) : valid D i := by
  by_cases h160_176 : i < 168
  · by_cases h160_168 : i < 164
    · by_cases h160_164 : i < 162
      · by_cases h160_162 : i < 161
        · have e : i = 160 := by omega
          subst i
          exact ok160
        · have e : i = 161 := by omega
          subst i
          exact ok161
      · by_cases h162_164 : i < 163
        · have e : i = 162 := by omega
          subst i
          exact ok162
        · have e : i = 163 := by omega
          subst i
          exact ok163
    · by_cases h164_168 : i < 166
      · by_cases h164_166 : i < 165
        · have e : i = 164 := by omega
          subst i
          exact ok164
        · have e : i = 165 := by omega
          subst i
          exact ok165
      · by_cases h166_168 : i < 167
        · have e : i = 166 := by omega
          subst i
          exact ok166
        · have e : i = 167 := by omega
          subst i
          exact ok167
  · by_cases h168_176 : i < 172
    · by_cases h168_172 : i < 170
      · by_cases h168_170 : i < 169
        · have e : i = 168 := by omega
          subst i
          exact ok168
        · have e : i = 169 := by omega
          subst i
          exact ok169
      · by_cases h170_172 : i < 171
        · have e : i = 170 := by omega
          subst i
          exact ok170
        · have e : i = 171 := by omega
          subst i
          exact ok171
    · by_cases h172_176 : i < 174
      · by_cases h172_174 : i < 173
        · have e : i = 172 := by omega
          subst i
          exact ok172
        · have e : i = 173 := by omega
          subst i
          exact ok173
      · by_cases h174_176 : i < 175
        · have e : i = 174 := by omega
          subst i
          exact ok174
        · have e : i = 175 := by omega
          subst i
          exact ok175
end HaarK33Data
