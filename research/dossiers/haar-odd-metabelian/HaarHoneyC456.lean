import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok456 : valid D 456 := by decide +kernel
private theorem ok457 : valid D 457 := by decide +kernel
private theorem ok458 : valid D 458 := by decide +kernel
private theorem ok459 : valid D 459 := by decide +kernel
private theorem ok460 : valid D 460 := by decide +kernel
private theorem ok461 : valid D 461 := by decide +kernel
private theorem ok462 : valid D 462 := by decide +kernel
private theorem ok463 : valid D 463 := by decide +kernel
private theorem ok464 : valid D 464 := by decide +kernel
private theorem ok465 : valid D 465 := by decide +kernel
private theorem ok466 : valid D 466 := by decide +kernel
private theorem ok467 : valid D 467 := by decide +kernel
private theorem ok468 : valid D 468 := by decide +kernel
private theorem ok469 : valid D 469 := by decide +kernel
private theorem ok470 : valid D 470 := by decide +kernel
private theorem ok471 : valid D 471 := by decide +kernel
private theorem ok472 : valid D 472 := by decide +kernel
private theorem ok473 : valid D 473 := by decide +kernel
private theorem ok474 : valid D 474 := by decide +kernel
private theorem ok475 : valid D 475 := by decide +kernel
private theorem ok476 : valid D 476 := by decide +kernel
private theorem ok477 : valid D 477 := by decide +kernel
private theorem ok478 : valid D 478 := by decide +kernel
private theorem ok479 : valid D 479 := by decide +kernel
theorem C456valid (i : Nat) (_lo : 456 ≤ i) (_hi : i < 480) : valid D i := by
  by_cases h456_480 : i < 468
  · by_cases h456_468 : i < 462
    · by_cases h456_462 : i < 459
      · by_cases h456_459 : i < 457
        · have e : i = 456 := by omega
          subst i
          exact ok456
        · by_cases h457_459 : i < 458
          · have e : i = 457 := by omega
            subst i
            exact ok457
          · have e : i = 458 := by omega
            subst i
            exact ok458
      · by_cases h459_462 : i < 460
        · have e : i = 459 := by omega
          subst i
          exact ok459
        · by_cases h460_462 : i < 461
          · have e : i = 460 := by omega
            subst i
            exact ok460
          · have e : i = 461 := by omega
            subst i
            exact ok461
    · by_cases h462_468 : i < 465
      · by_cases h462_465 : i < 463
        · have e : i = 462 := by omega
          subst i
          exact ok462
        · by_cases h463_465 : i < 464
          · have e : i = 463 := by omega
            subst i
            exact ok463
          · have e : i = 464 := by omega
            subst i
            exact ok464
      · by_cases h465_468 : i < 466
        · have e : i = 465 := by omega
          subst i
          exact ok465
        · by_cases h466_468 : i < 467
          · have e : i = 466 := by omega
            subst i
            exact ok466
          · have e : i = 467 := by omega
            subst i
            exact ok467
  · by_cases h468_480 : i < 474
    · by_cases h468_474 : i < 471
      · by_cases h468_471 : i < 469
        · have e : i = 468 := by omega
          subst i
          exact ok468
        · by_cases h469_471 : i < 470
          · have e : i = 469 := by omega
            subst i
            exact ok469
          · have e : i = 470 := by omega
            subst i
            exact ok470
      · by_cases h471_474 : i < 472
        · have e : i = 471 := by omega
          subst i
          exact ok471
        · by_cases h472_474 : i < 473
          · have e : i = 472 := by omega
            subst i
            exact ok472
          · have e : i = 473 := by omega
            subst i
            exact ok473
    · by_cases h474_480 : i < 477
      · by_cases h474_477 : i < 475
        · have e : i = 474 := by omega
          subst i
          exact ok474
        · by_cases h475_477 : i < 476
          · have e : i = 475 := by omega
            subst i
            exact ok475
          · have e : i = 476 := by omega
            subst i
            exact ok476
      · by_cases h477_480 : i < 478
        · have e : i = 477 := by omega
          subst i
          exact ok477
        · by_cases h478_480 : i < 479
          · have e : i = 478 := by omega
            subst i
            exact ok478
          · have e : i = 479 := by omega
            subst i
            exact ok479
end HaarHoneyData
