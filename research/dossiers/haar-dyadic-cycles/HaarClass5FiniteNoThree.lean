import HaarClass5OddNoThree

namespace HaarClass5FiniteNoThree
open HaarAllNoncommuting HaarTwoKernel HaarClass4Generate HaarUniversal36

variable {G H : Type*} [Group G] [Group H]

theorem lift_base (φ : G →* H) (x y : G) {m : ℕ} (two : BoundedTwo φ m)
    (base : φ x≠1 → φ y≠1 → φ x≠φ y →
      ∃ e : ℕ, 2≤e ∧ e≤6 ∧ HasCycle (φ x) (φ y) (2^e))
    (hx : x≠1) (hy : y≠1) (hxy : x≠y) :
    ∃ j, 2≤j ∧ j≤6+m ∧ HasCycle x y (2^j) := by
  by_cases h1 : φ x=1
  · obtain ⟨j,l,u,V,vi,va⟩ := collapsed_pair φ 1 x two (Ne.symm hx) (by simpa using h1.symm)
    exact ⟨j,l,by omega,V,vi,fun i => incl_left x y _ _ (va i)⟩
  by_cases h2 : φ y=1
  · obtain ⟨j,l,u,V,vi,va⟩ := collapsed_pair φ 1 y two (Ne.symm hy) (by simpa using h2.symm)
    exact ⟨j,l,by omega,V,vi,fun i => incl_right x y _ _ (va i)⟩
  by_cases h3 : φ x=φ y
  · obtain ⟨j,l,u,ha⟩ := collapsed_pair φ x y two hxy h3
    exact ⟨j,l,by omega,ha⟩
  obtain ⟨e,el,eh,w⟩ := base h1 h2 h3
  obtain ⟨j,jm,hj⟩ := lift_cycle φ x y two w
  exact ⟨e+j,by omega,by omega,hj⟩

theorem normalized [Finite G] (nil : L G 5=⊥) (n3 : ¬3∣Nat.card G)
    (x y : G) (hx : x≠1) (hy : y≠1) (hxy : x≠y) :
    ∃ j, 2≤j ∧ j≤6+Nat.factorization (Nat.card G) 2 ∧ HasCycle x y (2^j) := by
  classical
  let : Group.IsNilpotent G := Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨5,nil⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 G := Classical.arbitrary _
  let S : Subgroup G := P
  let : S.Normal := by change (P : Subgroup G).Normal; infer_instance
  let f := QuotientGroup.mk' S
  have cardBound : Nat.card f.ker ∣ 2^Nat.factorization (Nat.card G) 2 := by
    change Nat.card (QuotientGroup.mk' S).ker ∣ _
    rw [QuotientGroup.ker_mk']
    exact (P.card_eq_multiplicity).dvd
  have odd : Odd (Nat.card (G ⧸ S)) := by
    rw [← Nat.not_even_iff_odd,even_iff_two_dvd,← S.index_eq_card]
    exact P.not_dvd_index
  have not_three : ¬3∣Nat.card (G ⧸ S) := fun h => n3 (h.trans S.card_quotient_dvd_card)
  have cls : L (G ⧸ S) 5=⊥ := by
    have M : (L G 5).map f = L (G ⧸ S) 5 := map_ls f (QuotientGroup.mk'_surjective S) 5
    rw [← M,nil,Subgroup.map_bot]
  exact lift_base f x y (card_two_bound f _ cardBound)
    (HaarClass5OddNoThree.normalized cls odd not_three (f x) (f y)) hx hy hxy

/-- The shortest dyadic cycle has length at most 64 times the Sylow 2-subgroup
order for any three distinct ports in a finite class-at-most-five group of
order prime to 3. -/
theorem any_ports [Finite G] (nil : L G 5=⊥) (n3 : ¬3∣Nat.card G)
    (r s t : G) (hr : r≠s) (ht : r≠t) (hs : s≠t) :
    ∃ j, 2≤j ∧ j≤6+Nat.factorization (Nat.card G) 2 ∧ HaarAnyPorts.HasPortCycle r s t (2^j) := by
  obtain ⟨a,b,c⟩ := HaarAnyPorts.as_three r s t hr ht hs
  obtain ⟨e,el,eh,w⟩ := normalized nil n3 (s*r⁻¹) (t*r⁻¹) a b c
  exact ⟨e,el,eh,HaarAnyPorts.map_cycle r s t w⟩

end HaarClass5FiniteNoThree
#print axioms HaarClass5FiniteNoThree.any_ports
