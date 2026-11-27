import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok408 : valid D 408 := by decide +kernel
private theorem ok409 : valid D 409 := by decide +kernel
private theorem ok410 : valid D 410 := by decide +kernel
private theorem ok411 : valid D 411 := by decide +kernel
private theorem ok412 : valid D 412 := by decide +kernel
private theorem ok413 : valid D 413 := by decide +kernel
private theorem ok414 : valid D 414 := by decide +kernel
private theorem ok415 : valid D 415 := by decide +kernel
private theorem ok416 : valid D 416 := by decide +kernel
private theorem ok417 : valid D 417 := by decide +kernel
private theorem ok418 : valid D 418 := by decide +kernel
private theorem ok419 : valid D 419 := by decide +kernel
private theorem ok420 : valid D 420 := by decide +kernel
private theorem ok421 : valid D 421 := by decide +kernel
private theorem ok422 : valid D 422 := by decide +kernel
private theorem ok423 : valid D 423 := by decide +kernel
private theorem ok424 : valid D 424 := by decide +kernel
private theorem ok425 : valid D 425 := by decide +kernel
private theorem ok426 : valid D 426 := by decide +kernel
private theorem ok427 : valid D 427 := by decide +kernel
private theorem ok428 : valid D 428 := by decide +kernel
private theorem ok429 : valid D 429 := by decide +kernel
private theorem ok430 : valid D 430 := by decide +kernel
private theorem ok431 : valid D 431 := by decide +kernel
theorem C408valid (i : Nat) (_lo : 408 ≤ i) (_hi : i < 432) : valid D i := by
  by_cases h408_432 : i < 420
  · by_cases h408_420 : i < 414
    · by_cases h408_414 : i < 411
      · by_cases h408_411 : i < 409
        · have e : i = 408 := by omega
          subst i
          exact ok408
        · by_cases h409_411 : i < 410
          · have e : i = 409 := by omega
            subst i
            exact ok409
          · have e : i = 410 := by omega
            subst i
            exact ok410
      · by_cases h411_414 : i < 412
        · have e : i = 411 := by omega
          subst i
          exact ok411
        · by_cases h412_414 : i < 413
          · have e : i = 412 := by omega
            subst i
            exact ok412
          · have e : i = 413 := by omega
            subst i
            exact ok413
    · by_cases h414_420 : i < 417
      · by_cases h414_417 : i < 415
        · have e : i = 414 := by omega
          subst i
          exact ok414
        · by_cases h415_417 : i < 416
          · have e : i = 415 := by omega
            subst i
            exact ok415
          · have e : i = 416 := by omega
            subst i
            exact ok416
      · by_cases h417_420 : i < 418
        · have e : i = 417 := by omega
          subst i
          exact ok417
        · by_cases h418_420 : i < 419
          · have e : i = 418 := by omega
            subst i
            exact ok418
          · have e : i = 419 := by omega
            subst i
            exact ok419
  · by_cases h420_432 : i < 426
    · by_cases h420_426 : i < 423
      · by_cases h420_423 : i < 421
        · have e : i = 420 := by omega
          subst i
          exact ok420
        · by_cases h421_423 : i < 422
          · have e : i = 421 := by omega
            subst i
            exact ok421
          · have e : i = 422 := by omega
            subst i
            exact ok422
      · by_cases h423_426 : i < 424
        · have e : i = 423 := by omega
          subst i
          exact ok423
        · by_cases h424_426 : i < 425
          · have e : i = 424 := by omega
            subst i
            exact ok424
          · have e : i = 425 := by omega
            subst i
            exact ok425
    · by_cases h426_432 : i < 429
      · by_cases h426_429 : i < 427
        · have e : i = 426 := by omega
          subst i
          exact ok426
        · by_cases h427_429 : i < 428
          · have e : i = 427 := by omega
            subst i
            exact ok427
          · have e : i = 428 := by omega
            subst i
            exact ok428
      · by_cases h429_432 : i < 430
        · have e : i = 429 := by omega
          subst i
          exact ok429
        · by_cases h430_432 : i < 431
          · have e : i = 430 := by omega
            subst i
            exact ok430
          · have e : i = 431 := by omega
            subst i
            exact ok431
end HaarHoneyData
