import HaarMetaTorsionOneData
namespace HaarMetaTorsionOneData
open HaarMetaTorsionOneDAG HaarMetaTorsionOneVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok312 : valid D 312 := by decide +kernel
private theorem ok313 : valid D 313 := by decide +kernel
private theorem ok314 : valid D 314 := by decide +kernel
private theorem ok315 : valid D 315 := by decide +kernel
private theorem ok316 : valid D 316 := by decide +kernel
private theorem ok317 : valid D 317 := by decide +kernel
private theorem ok318 : valid D 318 := by decide +kernel
private theorem ok319 : valid D 319 := by decide +kernel
private theorem ok320 : valid D 320 := by decide +kernel
private theorem ok321 : valid D 321 := by decide +kernel
private theorem ok322 : valid D 322 := by decide +kernel
private theorem ok323 : valid D 323 := by decide +kernel
private theorem ok324 : valid D 324 := by decide +kernel
private theorem ok325 : valid D 325 := by decide +kernel
private theorem ok326 : valid D 326 := by decide +kernel
private theorem ok327 : valid D 327 := by decide +kernel
private theorem ok328 : valid D 328 := by decide +kernel
private theorem ok329 : valid D 329 := by decide +kernel
private theorem ok330 : valid D 330 := by decide +kernel
private theorem ok331 : valid D 331 := by decide +kernel
private theorem ok332 : valid D 332 := by decide +kernel
private theorem ok333 : valid D 333 := by decide +kernel
private theorem ok334 : valid D 334 := by decide +kernel
private theorem ok335 : valid D 335 := by decide +kernel
theorem C312valid (i : Nat) (_lo : 312 ≤ i) (_hi : i < 336) : valid D i := by
  by_cases h312_336 : i < 324
  · by_cases h312_324 : i < 318
    · by_cases h312_318 : i < 315
      · by_cases h312_315 : i < 313
        · have e : i = 312 := by omega
          subst i
          exact ok312
        · by_cases h313_315 : i < 314
          · have e : i = 313 := by omega
            subst i
            exact ok313
          · have e : i = 314 := by omega
            subst i
            exact ok314
      · by_cases h315_318 : i < 316
        · have e : i = 315 := by omega
          subst i
          exact ok315
        · by_cases h316_318 : i < 317
          · have e : i = 316 := by omega
            subst i
            exact ok316
          · have e : i = 317 := by omega
            subst i
            exact ok317
    · by_cases h318_324 : i < 321
      · by_cases h318_321 : i < 319
        · have e : i = 318 := by omega
          subst i
          exact ok318
        · by_cases h319_321 : i < 320
          · have e : i = 319 := by omega
            subst i
            exact ok319
          · have e : i = 320 := by omega
            subst i
            exact ok320
      · by_cases h321_324 : i < 322
        · have e : i = 321 := by omega
          subst i
          exact ok321
        · by_cases h322_324 : i < 323
          · have e : i = 322 := by omega
            subst i
            exact ok322
          · have e : i = 323 := by omega
            subst i
            exact ok323
  · by_cases h324_336 : i < 330
    · by_cases h324_330 : i < 327
      · by_cases h324_327 : i < 325
        · have e : i = 324 := by omega
          subst i
          exact ok324
        · by_cases h325_327 : i < 326
          · have e : i = 325 := by omega
            subst i
            exact ok325
          · have e : i = 326 := by omega
            subst i
            exact ok326
      · by_cases h327_330 : i < 328
        · have e : i = 327 := by omega
          subst i
          exact ok327
        · by_cases h328_330 : i < 329
          · have e : i = 328 := by omega
            subst i
            exact ok328
          · have e : i = 329 := by omega
            subst i
            exact ok329
    · by_cases h330_336 : i < 333
      · by_cases h330_333 : i < 331
        · have e : i = 330 := by omega
          subst i
          exact ok330
        · by_cases h331_333 : i < 332
          · have e : i = 331 := by omega
            subst i
            exact ok331
          · have e : i = 332 := by omega
            subst i
            exact ok332
      · by_cases h333_336 : i < 334
        · have e : i = 333 := by omega
          subst i
          exact ok333
        · by_cases h334_336 : i < 335
          · have e : i = 334 := by omega
            subst i
            exact ok334
          · have e : i = 335 := by omega
            subst i
            exact ok335
end HaarMetaTorsionOneData
