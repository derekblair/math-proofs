import HaarMetaS014Data
namespace HaarMetaS014Data
open HaarMetaS014DAG HaarMetaS014Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok384 : valid D 384 := by decide +kernel
private theorem ok385 : valid D 385 := by decide +kernel
private theorem ok386 : valid D 386 := by decide +kernel
private theorem ok387 : valid D 387 := by decide +kernel
private theorem ok388 : valid D 388 := by decide +kernel
private theorem ok389 : valid D 389 := by decide +kernel
private theorem ok390 : valid D 390 := by decide +kernel
private theorem ok391 : valid D 391 := by decide +kernel
private theorem ok392 : valid D 392 := by decide +kernel
private theorem ok393 : valid D 393 := by decide +kernel
private theorem ok394 : valid D 394 := by decide +kernel
private theorem ok395 : valid D 395 := by decide +kernel
private theorem ok396 : valid D 396 := by decide +kernel
private theorem ok397 : valid D 397 := by decide +kernel
private theorem ok398 : valid D 398 := by decide +kernel
private theorem ok399 : valid D 399 := by decide +kernel
private theorem ok400 : valid D 400 := by decide +kernel
private theorem ok401 : valid D 401 := by decide +kernel
private theorem ok402 : valid D 402 := by decide +kernel
private theorem ok403 : valid D 403 := by decide +kernel
private theorem ok404 : valid D 404 := by decide +kernel
private theorem ok405 : valid D 405 := by decide +kernel
private theorem ok406 : valid D 406 := by decide +kernel
private theorem ok407 : valid D 407 := by decide +kernel
theorem C384valid (i : Nat) (_lo : 384 ≤ i) (_hi : i < 408) : valid D i := by
  by_cases h384_408 : i < 396
  · by_cases h384_396 : i < 390
    · by_cases h384_390 : i < 387
      · by_cases h384_387 : i < 385
        · have e : i = 384 := by omega
          subst i
          exact ok384
        · by_cases h385_387 : i < 386
          · have e : i = 385 := by omega
            subst i
            exact ok385
          · have e : i = 386 := by omega
            subst i
            exact ok386
      · by_cases h387_390 : i < 388
        · have e : i = 387 := by omega
          subst i
          exact ok387
        · by_cases h388_390 : i < 389
          · have e : i = 388 := by omega
            subst i
            exact ok388
          · have e : i = 389 := by omega
            subst i
            exact ok389
    · by_cases h390_396 : i < 393
      · by_cases h390_393 : i < 391
        · have e : i = 390 := by omega
          subst i
          exact ok390
        · by_cases h391_393 : i < 392
          · have e : i = 391 := by omega
            subst i
            exact ok391
          · have e : i = 392 := by omega
            subst i
            exact ok392
      · by_cases h393_396 : i < 394
        · have e : i = 393 := by omega
          subst i
          exact ok393
        · by_cases h394_396 : i < 395
          · have e : i = 394 := by omega
            subst i
            exact ok394
          · have e : i = 395 := by omega
            subst i
            exact ok395
  · by_cases h396_408 : i < 402
    · by_cases h396_402 : i < 399
      · by_cases h396_399 : i < 397
        · have e : i = 396 := by omega
          subst i
          exact ok396
        · by_cases h397_399 : i < 398
          · have e : i = 397 := by omega
            subst i
            exact ok397
          · have e : i = 398 := by omega
            subst i
            exact ok398
      · by_cases h399_402 : i < 400
        · have e : i = 399 := by omega
          subst i
          exact ok399
        · by_cases h400_402 : i < 401
          · have e : i = 400 := by omega
            subst i
            exact ok400
          · have e : i = 401 := by omega
            subst i
            exact ok401
    · by_cases h402_408 : i < 405
      · by_cases h402_405 : i < 403
        · have e : i = 402 := by omega
          subst i
          exact ok402
        · by_cases h403_405 : i < 404
          · have e : i = 403 := by omega
            subst i
            exact ok403
          · have e : i = 404 := by omega
            subst i
            exact ok404
      · by_cases h405_408 : i < 406
        · have e : i = 405 := by omega
          subst i
          exact ok405
        · by_cases h406_408 : i < 407
          · have e : i = 406 := by omega
            subst i
            exact ok406
          · have e : i = 407 := by omega
            subst i
            exact ok407
end HaarMetaS014Data
