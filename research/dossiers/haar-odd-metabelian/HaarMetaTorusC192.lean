import HaarMetaTorusData
namespace HaarMetaTorusData
open HaarMetaTorusDAG HaarMetaTorusVoltage
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
private theorem ok208 : valid D 208 := by decide +kernel
private theorem ok209 : valid D 209 := by decide +kernel
private theorem ok210 : valid D 210 := by decide +kernel
private theorem ok211 : valid D 211 := by decide +kernel
private theorem ok212 : valid D 212 := by decide +kernel
private theorem ok213 : valid D 213 := by decide +kernel
private theorem ok214 : valid D 214 := by decide +kernel
private theorem ok215 : valid D 215 := by decide +kernel
private theorem ok216 : valid D 216 := by decide +kernel
private theorem ok217 : valid D 217 := by decide +kernel
private theorem ok218 : valid D 218 := by decide +kernel
private theorem ok219 : valid D 219 := by decide +kernel
private theorem ok220 : valid D 220 := by decide +kernel
private theorem ok221 : valid D 221 := by decide +kernel
private theorem ok222 : valid D 222 := by decide +kernel
private theorem ok223 : valid D 223 := by decide +kernel
theorem C192valid (i : Nat) (_lo : 192 ≤ i) (_hi : i < 224) : valid D i := by
  by_cases h192_224 : i < 208
  · by_cases h192_208 : i < 200
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
  · by_cases h208_224 : i < 216
    · by_cases h208_216 : i < 212
      · by_cases h208_212 : i < 210
        · by_cases h208_210 : i < 209
          · have e : i = 208 := by omega
            subst i
            exact ok208
          · have e : i = 209 := by omega
            subst i
            exact ok209
        · by_cases h210_212 : i < 211
          · have e : i = 210 := by omega
            subst i
            exact ok210
          · have e : i = 211 := by omega
            subst i
            exact ok211
      · by_cases h212_216 : i < 214
        · by_cases h212_214 : i < 213
          · have e : i = 212 := by omega
            subst i
            exact ok212
          · have e : i = 213 := by omega
            subst i
            exact ok213
        · by_cases h214_216 : i < 215
          · have e : i = 214 := by omega
            subst i
            exact ok214
          · have e : i = 215 := by omega
            subst i
            exact ok215
    · by_cases h216_224 : i < 220
      · by_cases h216_220 : i < 218
        · by_cases h216_218 : i < 217
          · have e : i = 216 := by omega
            subst i
            exact ok216
          · have e : i = 217 := by omega
            subst i
            exact ok217
        · by_cases h218_220 : i < 219
          · have e : i = 218 := by omega
            subst i
            exact ok218
          · have e : i = 219 := by omega
            subst i
            exact ok219
      · by_cases h220_224 : i < 222
        · by_cases h220_222 : i < 221
          · have e : i = 220 := by omega
            subst i
            exact ok220
          · have e : i = 221 := by omega
            subst i
            exact ok221
        · by_cases h222_224 : i < 223
          · have e : i = 222 := by omega
            subst i
            exact ok222
          · have e : i = 223 := by omega
            subst i
            exact ok223
end HaarMetaTorusData
