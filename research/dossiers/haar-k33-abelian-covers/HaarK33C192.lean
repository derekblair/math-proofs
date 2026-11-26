import HaarK33Data
namespace HaarK33Data
open HaarK33DAG HaarK33Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok192 : valid D 192 := by decide +kernel
private theorem ok193 : valid D 193 := by decide +kernel
private theorem ok194 : valid D 194 := by decide +kernel
private theorem ok195 : valid D 195 := by decide +kernel
private theorem ok196 : valid D 196 := by decide +kernel
private theorem ok197 : valid D 197 := by decide +kernel
private theorem ok198 : valid D 198 := by decide +kernel
private theorem ok199 : valid D 199 := by decide +kernel
private theorem ok200 : valid D 200 := by decide +kernel
private theorem ok201 : valid D 201 := by decide +kernel
private theorem ok202 : valid D 202 := by decide +kernel
private theorem ok203 : valid D 203 := by decide +kernel
private theorem ok204 : valid D 204 := by decide +kernel
private theorem ok205 : valid D 205 := by decide +kernel
private theorem ok206 : valid D 206 := by decide +kernel
private theorem ok207 : valid D 207 := by decide +kernel
theorem C192valid (i : Nat) (_lo : 192 ≤ i) (_hi : i < 208) : valid D i := by
  by_cases h192_208 : i < 200
  · by_cases h192_200 : i < 196
    · by_cases h192_196 : i < 194
      · by_cases h192_194 : i < 193
        · have e : i = 192 := by omega
          subst i
          exact ok192
        · have e : i = 193 := by omega
          subst i
          exact ok193
      · by_cases h194_196 : i < 195
        · have e : i = 194 := by omega
          subst i
          exact ok194
        · have e : i = 195 := by omega
          subst i
          exact ok195
    · by_cases h196_200 : i < 198
      · by_cases h196_198 : i < 197
        · have e : i = 196 := by omega
          subst i
          exact ok196
        · have e : i = 197 := by omega
          subst i
          exact ok197
      · by_cases h198_200 : i < 199
        · have e : i = 198 := by omega
          subst i
          exact ok198
        · have e : i = 199 := by omega
          subst i
          exact ok199
  · by_cases h200_208 : i < 204
    · by_cases h200_204 : i < 202
      · by_cases h200_202 : i < 201
        · have e : i = 200 := by omega
          subst i
          exact ok200
        · have e : i = 201 := by omega
          subst i
          exact ok201
      · by_cases h202_204 : i < 203
        · have e : i = 202 := by omega
          subst i
          exact ok202
        · have e : i = 203 := by omega
          subst i
          exact ok203
    · by_cases h204_208 : i < 206
      · by_cases h204_206 : i < 205
        · have e : i = 204 := by omega
          subst i
          exact ok204
        · have e : i = 205 := by omega
          subst i
          exact ok205
      · by_cases h206_208 : i < 207
        · have e : i = 206 := by omega
          subst i
          exact ok206
        · have e : i = 207 := by omega
          subst i
          exact ok207
end HaarK33Data
