import HaarMetaNineData
namespace HaarMetaNineData
open HaarMetaNineDAG HaarMetaNineVoltage
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
private theorem ok408 : valid D 408 := by decide +kernel
private theorem ok409 : valid D 409 := by decide +kernel
private theorem ok410 : valid D 410 := by decide +kernel
private theorem ok411 : valid D 411 := by decide +kernel
private theorem ok412 : valid D 412 := by decide +kernel
private theorem ok413 : valid D 413 := by decide +kernel
private theorem ok414 : valid D 414 := by decide +kernel
private theorem ok415 : valid D 415 := by decide +kernel
theorem C384valid (i : Nat) (_lo : 384 ≤ i) (_hi : i < 416) : valid D i := by
  by_cases h384_416 : i < 400
  · by_cases h384_400 : i < 392
    · by_cases h384_392 : i < 388
      · by_cases h384_388 : i < 386
        · by_cases h384_386 : i < 385
          · have e : i = 384 := by omega
            subst i
            exact ok384
          · have e : i = 385 := by omega
            subst i
            exact ok385
        · by_cases h386_388 : i < 387
          · have e : i = 386 := by omega
            subst i
            exact ok386
          · have e : i = 387 := by omega
            subst i
            exact ok387
      · by_cases h388_392 : i < 390
        · by_cases h388_390 : i < 389
          · have e : i = 388 := by omega
            subst i
            exact ok388
          · have e : i = 389 := by omega
            subst i
            exact ok389
        · by_cases h390_392 : i < 391
          · have e : i = 390 := by omega
            subst i
            exact ok390
          · have e : i = 391 := by omega
            subst i
            exact ok391
    · by_cases h392_400 : i < 396
      · by_cases h392_396 : i < 394
        · by_cases h392_394 : i < 393
          · have e : i = 392 := by omega
            subst i
            exact ok392
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
      · by_cases h396_400 : i < 398
        · by_cases h396_398 : i < 397
          · have e : i = 396 := by omega
            subst i
            exact ok396
          · have e : i = 397 := by omega
            subst i
            exact ok397
        · by_cases h398_400 : i < 399
          · have e : i = 398 := by omega
            subst i
            exact ok398
          · have e : i = 399 := by omega
            subst i
            exact ok399
  · by_cases h400_416 : i < 408
    · by_cases h400_408 : i < 404
      · by_cases h400_404 : i < 402
        · by_cases h400_402 : i < 401
          · have e : i = 400 := by omega
            subst i
            exact ok400
          · have e : i = 401 := by omega
            subst i
            exact ok401
        · by_cases h402_404 : i < 403
          · have e : i = 402 := by omega
            subst i
            exact ok402
          · have e : i = 403 := by omega
            subst i
            exact ok403
      · by_cases h404_408 : i < 406
        · by_cases h404_406 : i < 405
          · have e : i = 404 := by omega
            subst i
            exact ok404
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
    · by_cases h408_416 : i < 412
      · by_cases h408_412 : i < 410
        · by_cases h408_410 : i < 409
          · have e : i = 408 := by omega
            subst i
            exact ok408
          · have e : i = 409 := by omega
            subst i
            exact ok409
        · by_cases h410_412 : i < 411
          · have e : i = 410 := by omega
            subst i
            exact ok410
          · have e : i = 411 := by omega
            subst i
            exact ok411
      · by_cases h412_416 : i < 414
        · by_cases h412_414 : i < 413
          · have e : i = 412 := by omega
            subst i
            exact ok412
          · have e : i = 413 := by omega
            subst i
            exact ok413
        · by_cases h414_416 : i < 415
          · have e : i = 414 := by omega
            subst i
            exact ok414
          · have e : i = 415 := by omega
            subst i
            exact ok415
end HaarMetaNineData
