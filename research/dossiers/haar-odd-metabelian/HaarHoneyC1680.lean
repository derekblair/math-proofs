import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1680 : valid D 1680 := by decide +kernel
private theorem ok1681 : valid D 1681 := by decide +kernel
private theorem ok1682 : valid D 1682 := by decide +kernel
private theorem ok1683 : valid D 1683 := by decide +kernel
private theorem ok1684 : valid D 1684 := by decide +kernel
private theorem ok1685 : valid D 1685 := by decide +kernel
private theorem ok1686 : valid D 1686 := by decide +kernel
private theorem ok1687 : valid D 1687 := by decide +kernel
private theorem ok1688 : valid D 1688 := by decide +kernel
private theorem ok1689 : valid D 1689 := by decide +kernel
private theorem ok1690 : valid D 1690 := by decide +kernel
private theorem ok1691 : valid D 1691 := by decide +kernel
private theorem ok1692 : valid D 1692 := by decide +kernel
private theorem ok1693 : valid D 1693 := by decide +kernel
private theorem ok1694 : valid D 1694 := by decide +kernel
private theorem ok1695 : valid D 1695 := by decide +kernel
private theorem ok1696 : valid D 1696 := by decide +kernel
private theorem ok1697 : valid D 1697 := by decide +kernel
private theorem ok1698 : valid D 1698 := by decide +kernel
private theorem ok1699 : valid D 1699 := by decide +kernel
private theorem ok1700 : valid D 1700 := by decide +kernel
private theorem ok1701 : valid D 1701 := by decide +kernel
private theorem ok1702 : valid D 1702 := by decide +kernel
private theorem ok1703 : valid D 1703 := by decide +kernel
theorem C1680valid (i : Nat) (_lo : 1680 ≤ i) (_hi : i < 1704) : valid D i := by
  by_cases h1680_1704 : i < 1692
  · by_cases h1680_1692 : i < 1686
    · by_cases h1680_1686 : i < 1683
      · by_cases h1680_1683 : i < 1681
        · have e : i = 1680 := by omega
          subst i
          exact ok1680
        · by_cases h1681_1683 : i < 1682
          · have e : i = 1681 := by omega
            subst i
            exact ok1681
          · have e : i = 1682 := by omega
            subst i
            exact ok1682
      · by_cases h1683_1686 : i < 1684
        · have e : i = 1683 := by omega
          subst i
          exact ok1683
        · by_cases h1684_1686 : i < 1685
          · have e : i = 1684 := by omega
            subst i
            exact ok1684
          · have e : i = 1685 := by omega
            subst i
            exact ok1685
    · by_cases h1686_1692 : i < 1689
      · by_cases h1686_1689 : i < 1687
        · have e : i = 1686 := by omega
          subst i
          exact ok1686
        · by_cases h1687_1689 : i < 1688
          · have e : i = 1687 := by omega
            subst i
            exact ok1687
          · have e : i = 1688 := by omega
            subst i
            exact ok1688
      · by_cases h1689_1692 : i < 1690
        · have e : i = 1689 := by omega
          subst i
          exact ok1689
        · by_cases h1690_1692 : i < 1691
          · have e : i = 1690 := by omega
            subst i
            exact ok1690
          · have e : i = 1691 := by omega
            subst i
            exact ok1691
  · by_cases h1692_1704 : i < 1698
    · by_cases h1692_1698 : i < 1695
      · by_cases h1692_1695 : i < 1693
        · have e : i = 1692 := by omega
          subst i
          exact ok1692
        · by_cases h1693_1695 : i < 1694
          · have e : i = 1693 := by omega
            subst i
            exact ok1693
          · have e : i = 1694 := by omega
            subst i
            exact ok1694
      · by_cases h1695_1698 : i < 1696
        · have e : i = 1695 := by omega
          subst i
          exact ok1695
        · by_cases h1696_1698 : i < 1697
          · have e : i = 1696 := by omega
            subst i
            exact ok1696
          · have e : i = 1697 := by omega
            subst i
            exact ok1697
    · by_cases h1698_1704 : i < 1701
      · by_cases h1698_1701 : i < 1699
        · have e : i = 1698 := by omega
          subst i
          exact ok1698
        · by_cases h1699_1701 : i < 1700
          · have e : i = 1699 := by omega
            subst i
            exact ok1699
          · have e : i = 1700 := by omega
            subst i
            exact ok1700
      · by_cases h1701_1704 : i < 1702
        · have e : i = 1701 := by omega
          subst i
          exact ok1701
        · by_cases h1702_1704 : i < 1703
          · have e : i = 1702 := by omega
            subst i
            exact ok1702
          · have e : i = 1703 := by omega
            subst i
            exact ok1703
end HaarHoneyData
