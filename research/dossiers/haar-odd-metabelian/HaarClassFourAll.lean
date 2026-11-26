import HaarClassFourOdd

namespace HaarClassFourAll
open HaarAllNoncommuting HaarTwoKernel HaarClass4Generate HaarClass4Structure HaarClassFourOdd

variable {G H : Type*} [Group G] [Group H]

theorem of_base (φ : G →* H) (x y : G) {m : ℕ} (two : BoundedTwo φ m)
    (base : φ x≠1 → φ y≠1 → φ x≠φ y →
      HasCycle (φ x) (φ y) 4 ∨ HasCycle (φ x) (φ y) 8 ∨
        HasCycle (φ x) (φ y) 16 ∨ HasCycle (φ x) (φ y) 32)
    (hx : x≠1) (hy : y≠1) (hxy : x≠y) :
    ∃ j, 2 ≤ j ∧ j ≤ 5+m ∧ HasCycle x y (2^j) := by
  by_cases h1 : φ x=1
  · obtain ⟨j,l,u,V,vi,va⟩ := collapsed_pair φ 1 x two (Ne.symm hx) (by simpa using h1.symm)
    exact ⟨j,l,by omega,V,vi,fun i => incl_left x y _ _ (va i)⟩
  by_cases h2 : φ y=1
  · obtain ⟨j,l,u,V,vi,va⟩ := collapsed_pair φ 1 y two (Ne.symm hy) (by simpa using h2.symm)
    exact ⟨j,l,by omega,V,vi,fun i => incl_right x y _ _ (va i)⟩
  by_cases h3 : φ x=φ y
  · obtain ⟨j,l,u,ha⟩ := collapsed_pair φ x y two hxy h3
    exact ⟨j,l,by omega,ha⟩
  have d := base h1 h2 h3
  have bd (r : ℕ) (l : 2 ≤ r) (u : r ≤ 5)
      (ha : HasCycle (φ x) (φ y) (2^r)) :
      ∃ j, 2 ≤ j ∧ j ≤ 5+m ∧ HasCycle x y (2^j) := by
    obtain ⟨j,jm,hj⟩ := lift_cycle φ x y two ha
    exact ⟨r+j,by omega,by omega,hj⟩
  rcases d with h|h|h|h
  · exact bd 2 (by decide) (by decide) h
  · exact bd 3 (by decide) (by decide) h
  · exact bd 4 (by decide) (by decide) h
  · exact bd 5 (by decide) (by decide) h

theorem finite_class_four [Finite G] (cl : LS G 4 = ⊥)
    (x y : G) (hx : x≠1) (hy : y≠1) (hxy : x≠y) :
    ∃ j, 2 ≤ j ∧ j ≤ 5+Nat.factorization (Nat.card G) 2 ∧ HasCycle x y (2^j) := by
  classical
  let : Group.IsNilpotent G := Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨4,cl⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 G := Classical.arbitrary _
  let S : Subgroup G := P
  let : S.Normal := by change (P : Subgroup G).Normal; infer_instance
  let φ := QuotientGroup.mk' S
  have hCard : Nat.card φ.ker ∣ 2^Nat.factorization (Nat.card G) 2 := by
    change Nat.card (QuotientGroup.mk' S).ker ∣ _
    rw [QuotientGroup.ker_mk']
    exact (P.card_eq_multiplicity).dvd
  have odd : Odd (Nat.card (G ⧸ S)) := by
    rw [← Nat.not_even_iff_odd,even_iff_two_dvd,← S.index_eq_card]
    exact P.not_dvd_index
  have hg : LS (G ⧸ S) 4=⊥ := by
    rw [← map_ls φ (QuotientGroup.mk'_surjective S) 4,cl,Subgroup.map_bot]
  exact of_base φ x y (card_two_bound φ _ hCard)
    (odd_class_four hg (φ x) (φ y) odd) hx hy hxy

end HaarClassFourAll

#print axioms HaarClassFourAll.finite_class_four
