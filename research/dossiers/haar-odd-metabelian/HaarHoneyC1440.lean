import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1440 : valid D 1440 := by decide +kernel
private theorem ok1441 : valid D 1441 := by decide +kernel
private theorem ok1442 : valid D 1442 := by decide +kernel
private theorem ok1443 : valid D 1443 := by decide +kernel
private theorem ok1444 : valid D 1444 := by decide +kernel
private theorem ok1445 : valid D 1445 := by decide +kernel
private theorem ok1446 : valid D 1446 := by decide +kernel
private theorem ok1447 : valid D 1447 := by decide +kernel
private theorem ok1448 : valid D 1448 := by decide +kernel
private theorem ok1449 : valid D 1449 := by decide +kernel
private theorem ok1450 : valid D 1450 := by decide +kernel
private theorem ok1451 : valid D 1451 := by decide +kernel
private theorem ok1452 : valid D 1452 := by decide +kernel
private theorem ok1453 : valid D 1453 := by decide +kernel
private theorem ok1454 : valid D 1454 := by decide +kernel
private theorem ok1455 : valid D 1455 := by decide +kernel
private theorem ok1456 : valid D 1456 := by decide +kernel
private theorem ok1457 : valid D 1457 := by decide +kernel
private theorem ok1458 : valid D 1458 := by decide +kernel
private theorem ok1459 : valid D 1459 := by decide +kernel
private theorem ok1460 : valid D 1460 := by decide +kernel
private theorem ok1461 : valid D 1461 := by decide +kernel
private theorem ok1462 : valid D 1462 := by decide +kernel
private theorem ok1463 : valid D 1463 := by decide +kernel
theorem C1440valid (i : Nat) (_lo : 1440 ≤ i) (_hi : i < 1464) : valid D i := by
  by_cases h1440_1464 : i < 1452
  · by_cases h1440_1452 : i < 1446
    · by_cases h1440_1446 : i < 1443
      · by_cases h1440_1443 : i < 1441
        · have e : i = 1440 := by omega
          subst i
          exact ok1440
        · by_cases h1441_1443 : i < 1442
          · have e : i = 1441 := by omega
            subst i
            exact ok1441
          · have e : i = 1442 := by omega
            subst i
            exact ok1442
      · by_cases h1443_1446 : i < 1444
        · have e : i = 1443 := by omega
          subst i
          exact ok1443
        · by_cases h1444_1446 : i < 1445
          · have e : i = 1444 := by omega
            subst i
            exact ok1444
          · have e : i = 1445 := by omega
            subst i
            exact ok1445
    · by_cases h1446_1452 : i < 1449
      · by_cases h1446_1449 : i < 1447
        · have e : i = 1446 := by omega
          subst i
          exact ok1446
        · by_cases h1447_1449 : i < 1448
          · have e : i = 1447 := by omega
            subst i
            exact ok1447
          · have e : i = 1448 := by omega
            subst i
            exact ok1448
      · by_cases h1449_1452 : i < 1450
        · have e : i = 1449 := by omega
          subst i
          exact ok1449
        · by_cases h1450_1452 : i < 1451
          · have e : i = 1450 := by omega
            subst i
            exact ok1450
          · have e : i = 1451 := by omega
            subst i
            exact ok1451
  · by_cases h1452_1464 : i < 1458
    · by_cases h1452_1458 : i < 1455
      · by_cases h1452_1455 : i < 1453
        · have e : i = 1452 := by omega
          subst i
          exact ok1452
        · by_cases h1453_1455 : i < 1454
          · have e : i = 1453 := by omega
            subst i
            exact ok1453
          · have e : i = 1454 := by omega
            subst i
            exact ok1454
      · by_cases h1455_1458 : i < 1456
        · have e : i = 1455 := by omega
          subst i
          exact ok1455
        · by_cases h1456_1458 : i < 1457
          · have e : i = 1456 := by omega
            subst i
            exact ok1456
          · have e : i = 1457 := by omega
            subst i
            exact ok1457
    · by_cases h1458_1464 : i < 1461
      · by_cases h1458_1461 : i < 1459
        · have e : i = 1458 := by omega
          subst i
          exact ok1458
        · by_cases h1459_1461 : i < 1460
          · have e : i = 1459 := by omega
            subst i
            exact ok1459
          · have e : i = 1460 := by omega
            subst i
            exact ok1460
      · by_cases h1461_1464 : i < 1462
        · have e : i = 1461 := by omega
          subst i
          exact ok1461
        · by_cases h1462_1464 : i < 1463
          · have e : i = 1462 := by omega
            subst i
            exact ok1462
          · have e : i = 1463 := by omega
            subst i
            exact ok1463
end HaarHoneyData
