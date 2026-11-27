import HaarMetaS025Data
namespace HaarMetaS025Data
open HaarMetaS025DAG HaarMetaS025Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok408 : valid D 408 := by decide +kernel
private theorem ok409 : valid D 409 := by decide +kernel
private theorem ok410 : valid D 410 := by decide +kernel
private theorem ok411 : valid D 411 := by decide +kernel
private theorem ok412 : valid D 412 := by decide +kernel
private theorem ok413 : valid D 413 := by decide +kernel
private theorem ok414 : valid D 414 := by decide +kernel
theorem C408valid (i : Nat) (_lo : 408 ≤ i) (_hi : i < 415) : valid D i := by
  by_cases h408_415 : i < 411
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
  · by_cases h411_415 : i < 413
    · by_cases h411_413 : i < 412
      · have e : i = 411 := by omega
        subst i
        exact ok411
      · have e : i = 412 := by omega
        subst i
        exact ok412
    · by_cases h413_415 : i < 414
      · have e : i = 413 := by omega
        subst i
        exact ok413
      · have e : i = 414 := by omega
        subst i
        exact ok414
end HaarMetaS025Data
