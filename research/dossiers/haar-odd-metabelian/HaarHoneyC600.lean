import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok600 : valid D 600 := by decide +kernel
private theorem ok601 : valid D 601 := by decide +kernel
private theorem ok602 : valid D 602 := by decide +kernel
private theorem ok603 : valid D 603 := by decide +kernel
private theorem ok604 : valid D 604 := by decide +kernel
private theorem ok605 : valid D 605 := by decide +kernel
private theorem ok606 : valid D 606 := by decide +kernel
private theorem ok607 : valid D 607 := by decide +kernel
private theorem ok608 : valid D 608 := by decide +kernel
private theorem ok609 : valid D 609 := by decide +kernel
private theorem ok610 : valid D 610 := by decide +kernel
private theorem ok611 : valid D 611 := by decide +kernel
private theorem ok612 : valid D 612 := by decide +kernel
private theorem ok613 : valid D 613 := by decide +kernel
private theorem ok614 : valid D 614 := by decide +kernel
private theorem ok615 : valid D 615 := by decide +kernel
private theorem ok616 : valid D 616 := by decide +kernel
private theorem ok617 : valid D 617 := by decide +kernel
private theorem ok618 : valid D 618 := by decide +kernel
private theorem ok619 : valid D 619 := by decide +kernel
private theorem ok620 : valid D 620 := by decide +kernel
private theorem ok621 : valid D 621 := by decide +kernel
private theorem ok622 : valid D 622 := by decide +kernel
private theorem ok623 : valid D 623 := by decide +kernel
theorem C600valid (i : Nat) (_lo : 600 ≤ i) (_hi : i < 624) : valid D i := by
  by_cases h600_624 : i < 612
  · by_cases h600_612 : i < 606
    · by_cases h600_606 : i < 603
      · by_cases h600_603 : i < 601
        · have e : i = 600 := by omega
          subst i
          exact ok600
        · by_cases h601_603 : i < 602
          · have e : i = 601 := by omega
            subst i
            exact ok601
          · have e : i = 602 := by omega
            subst i
            exact ok602
      · by_cases h603_606 : i < 604
        · have e : i = 603 := by omega
          subst i
          exact ok603
        · by_cases h604_606 : i < 605
          · have e : i = 604 := by omega
            subst i
            exact ok604
          · have e : i = 605 := by omega
            subst i
            exact ok605
    · by_cases h606_612 : i < 609
      · by_cases h606_609 : i < 607
        · have e : i = 606 := by omega
          subst i
          exact ok606
        · by_cases h607_609 : i < 608
          · have e : i = 607 := by omega
            subst i
            exact ok607
          · have e : i = 608 := by omega
            subst i
            exact ok608
      · by_cases h609_612 : i < 610
        · have e : i = 609 := by omega
          subst i
          exact ok609
        · by_cases h610_612 : i < 611
          · have e : i = 610 := by omega
            subst i
            exact ok610
          · have e : i = 611 := by omega
            subst i
            exact ok611
  · by_cases h612_624 : i < 618
    · by_cases h612_618 : i < 615
      · by_cases h612_615 : i < 613
        · have e : i = 612 := by omega
          subst i
          exact ok612
        · by_cases h613_615 : i < 614
          · have e : i = 613 := by omega
            subst i
            exact ok613
          · have e : i = 614 := by omega
            subst i
            exact ok614
      · by_cases h615_618 : i < 616
        · have e : i = 615 := by omega
          subst i
          exact ok615
        · by_cases h616_618 : i < 617
          · have e : i = 616 := by omega
            subst i
            exact ok616
          · have e : i = 617 := by omega
            subst i
            exact ok617
    · by_cases h618_624 : i < 621
      · by_cases h618_621 : i < 619
        · have e : i = 618 := by omega
          subst i
          exact ok618
        · by_cases h619_621 : i < 620
          · have e : i = 619 := by omega
            subst i
            exact ok619
          · have e : i = 620 := by omega
            subst i
            exact ok620
      · by_cases h621_624 : i < 622
        · have e : i = 621 := by omega
          subst i
          exact ok621
        · by_cases h622_624 : i < 623
          · have e : i = 622 := by omega
            subst i
            exact ok622
          · have e : i = 623 := by omega
            subst i
            exact ok623
end HaarHoneyData
