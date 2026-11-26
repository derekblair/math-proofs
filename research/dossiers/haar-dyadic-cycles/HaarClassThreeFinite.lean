import HaarTwoKernel
import Mathlib.GroupTheory.Nilpotent

namespace HaarClassThreeFinite

open HaarAllNoncommuting
open Subgroup

variable {G H : Type*} [Group G] [Group H]

theorem fourth_is_fourth :
    (⊤ : Subgroup G).lowerCentralSeries 3 = ⁅HaarClass3Odd.gamma3 G, (⊤ : Subgroup G)⁆ := by
  have e : (⊤ : Subgroup G).lowerCentralSeries 2 = HaarClass3Odd.gamma3 G := by
    rw [show (2:ℕ)=1+1 by decide,Subgroup.lowerCentralSeries_succ,Subgroup.top_lowerCentralSeries_one]
    rfl
  exact congrArg (fun T : Subgroup G => ⁅T,(⊤ : Subgroup G)⁆) e

theorem quotient_class (φ : G →* H) (onto : Function.Surjective φ)
    (h : (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥) :
    (⊤ : Subgroup H).lowerCentralSeries 3 = ⊥ := by
  have e := map_lowerCentralSeries (S:=(⊤ : Subgroup G)) φ 3
  rw [h,Subgroup.map_bot,Subgroup.map_top, MonoidHom.range_eq_top.mpr onto] at e
  exact e.symm

theorem finite_class_three [Finite G] (cl : (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥)
    (x y : G) (hx : x≠1) (hy : y≠1) (hxy : x≠y) :
    ∃ j, 2 ≤ j ∧ j ≤ 5+Nat.factorization (Nat.card G) 2 ∧ HasCycle x y (2^j) := by
  classical
  let : Group.IsNilpotent G := Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨3,cl⟩
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
  have hg := quotient_class φ (QuotientGroup.mk'_surjective S) cl
  exact HaarTwoKernel.overall φ x y (HaarTwoKernel.card_two_bound φ _ hCard) odd
    (by rw [← fourth_is_fourth (G:=G ⧸ S)]; exact hg) hx hy hxy

end HaarClassThreeFinite

#print axioms HaarClassThreeFinite.finite_class_three
