import HaarClass5GirthUpper
import HaarCycleEven
import HaarClass5DyadicHighGirth
import HaarMatrix31ShortBound
import HaarMatrix31Card
import HaarOwnerF31S9T8Complete

namespace HaarClass5SharpGirth
open HaarMatrix31Core HaarAllNoncommuting

theorem odd_order : Odd (Nat.card UT) := by rw [HaarMatrix31Card.unitriangular_card]; decide

theorem no_even_below36 (k : ℕ) (lo : 4 ≤ k) (hi : k < 36) (he : Even k) :
    ¬ HasCycle x y k := by
  obtain ⟨j, e⟩ := he
  have E : k = 2*j := by omega
  rw [E]
  exact HaarMatrix31ShortBound.halfDiameterBound HaarOwnerPayload.exact_nodup_F31S9T8 j (by omega) (by omega)

theorem has36 : HasCycle x y 36 := by
  obtain ⟨hx,hy,hxy⟩ := distinct
  obtain ⟨k,lo,hi,even,cycle⟩ := HaarClass5GirthUpper.even_cycle_le36 x y hx hy hxy
    HaarMatrix31Filtration.class_at_most_five
  by_cases h : k=36
  · simpa only [h] using cycle
  · exact False.elim (no_even_below36 k lo (by omega) even cycle)

theorem has64 : HasCycle x y 64 := by
  obtain ⟨hx,hy,hxy⟩ := distinct
  exact HaarClass5DyadicHighGirth.highGirth_has64 HaarMatrix31Filtration.class_at_most_five x y hx hy hxy
    (fun k l h e => no_even_below36 k l (by omega) e)

theorem not_class_four : (⊤ : Subgroup UT).lowerCentralSeries 4 ≠ ⊥ := by
  intro h
  obtain ⟨hx,hy,hxy⟩ := distinct
  rcases HaarClassFourOdd.odd_class_four h x y odd_order hx hy hxy with h4|h8|h16|h32
  · exact no_even_below36 4 (by decide) (by decide) (by decide) h4
  · exact no_even_below36 8 (by decide) (by decide) (by decide) h8
  · exact no_even_below36 16 (by decide) (by decide) (by decide) h16
  · exact no_even_below36 32 (by decide) (by decide) (by decide) h32

/-- A shortest cycle has length 36, and a shortest dyadic cycle has length 64.
The lower limits exclude the degenerate length-two cyclic walk. -/
theorem exact_girth_and_dyadic :
    HasCycle x y 36 ∧ (∀ k, 3≤k → k<36 → ¬HasCycle x y k) ∧
    HasCycle x y 64 ∧ (∀ j, 2≤j → j<6 → ¬HasCycle x y (2^j)) := by
  refine ⟨has36, ?_, has64, ?_⟩
  · intro k lo hi hc
    have even := HaarCycleEven.even_positive (by omega) hc
    obtain ⟨j, hj⟩ := even
    exact no_even_below36 k (by omega) hi ⟨j,hj⟩ hc
  · intro j lo hi
    interval_cases j <;> exact no_even_below36 _ (by decide) (by decide) (by decide)

end HaarClass5SharpGirth
#print axioms HaarClass5SharpGirth.has36
#print axioms HaarClass5SharpGirth.has64
#print axioms HaarClass5SharpGirth.not_class_four
#print axioms HaarClass5SharpGirth.exact_girth_and_dyadic
