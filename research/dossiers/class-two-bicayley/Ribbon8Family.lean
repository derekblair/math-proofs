import Ribbon8Graph
import Ribbon8Algebra

namespace Ribbon8
open Ribbon5Bridge HaarClass4Structure HaarClass4Generate HaarClass4Ports RibbonClass4Fallback HaarUniversal36
open scoped commutatorElement
variable {G : Type*} [Group G]

/-- Local variant; the projected commutator avoids small orders. -/
theorem local_bound (nil : LS G 8=⊥) (x y : G)
    (good : ∀ k : Nat, 1≤k → k≤7 → (QuotientGroup.mk' (LS G 2) (portC x y))^k ≠ 1) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 ∨ Ribbon.Cycle x y 128 := by
  have C := commute nil x y
  apply cases_of_good x y good C
  intro nz eq
  have H : Commute (U x y) (R x y) := eq.symm ▸ C.symm
  apply nz
  rw [z_conjugate,H.commutator_eq,mul_one,inv_mul_cancel]

private theorem comm_if_projected_trivial (nil : LS G 8=⊥) (x y : G)
    (gen : Generates x y) (hc : portC x y∈LS G 2) : portC x y=1 := by
  let S := LS G 2
  let φ := QuotientGroup.mk' S
  have g := map_gen φ (QuotientGroup.mk'_surjective S) gen
  have r : Commute (φ x) (φ y) := by
    have C : φ (portC x y)=1 := (QuotientGroup.eq_one_iff _).mpr hc
    change φ x*φ y=φ y*φ x
    simpa only [map_mul,C,mul_one] using congrArg φ (ports_xy x y)
  let : IsMulCommutative (G ⧸ S) := gen_comm _ _ g r
  have zero : LS (G ⧸ S) 1=⊥ :=
    Subgroup.top_lowerCentralSeries_one.trans (commutator_eq_bot (G ⧸ S))
  have h := map_ls φ (QuotientGroup.mk'_surjective S) 1
  rw [zero,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at h
  have d : LS G 1=LS G 2 :=
    le_antisymm h ((Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G)) (by decide : 1≤2))
  let step : Subgroup G → Subgroup G := fun H => ⁅H,(⊤ : Subgroup G)⁆
  have d₂ : LS G 2=LS G 3 := congrArg step d
  have d₃ : LS G 3=LS G 4 := congrArg step d₂
  have d₄ : LS G 4=LS G 5 := congrArg step d₃
  have d₅ : LS G 5=LS G 6 := congrArg step d₄
  have d₆ : LS G 6=LS G 7 := congrArg step d₅
  have d₇ : LS G 7=LS G 8 := congrArg step d₆
  have all := d.trans (d₂.trans (d₃.trans (d₄.trans (d₅.trans (d₆.trans (d₇.trans nil))))))
  have hC := layer_c x y
  rw [all,Subgroup.mem_bot] at hC
  exact hC

private theorem generated_bound [Finite G] (nil : LS G 8=⊥) (x y : G)
    (gen : Generates x y) (cop : Nat.Coprime (Nat.card G) 420) (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨
      Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 ∨ Ribbon.Cycle x y 128 := by
  have odd := (cop.of_dvd_right (by decide : 2∣420)).odd_of_right
  by_cases C : portC x y∈LS G 2
  · have h := comm_if_projected_trivial nil x y gen C
    have z : Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 :=
      Ribbon.class2_pair x y (portC x y) (h ▸ Commute.one_left x) (h ▸ Commute.one_left y)
        (ports_xy x y) hx (by simpa only [pow_two] using HaarClass3Odd.odd_no_involution odd hy)
    exact z.imp_right (fun z => z.imp_right Or.inl)
  · have D : (QuotientGroup.mk' (LS G 2) (portC x y))≠1 :=
      fun e => C ((QuotientGroup.eq_one_iff _).mp e)
    have M := cop.of_dvd_left ((LS G 2).card_quotient_dvd_card)
    exact Or.inr (Or.inr (Or.inr (local_bound nil x y (card_good _ D M))))

/-- A 128 bound through class eight for orders prime to 2,3,5,7. -/
theorem prime_to_small_class8 [Finite G] (nil : LS G 8=⊥) (x y : G)
    (cop : Nat.Coprime (Nat.card G) 420) (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨
      Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 ∨ Ribbon.Cycle x y 128 := by
  let S := Pair x y
  have dvd : Nat.card S ∣ Nat.card G := S.card_subgroup_dvd_card
  have hx' : leftPort x y≠1 := fun e => hx (congrArg Subtype.val e)
  have hy' : rightPort x y≠1 := fun e => hy (congrArg Subtype.val e)
  rcases generated_bound (pair_nil x y 8 nil) _ _ (pair_generates x y) (cop.of_dvd_left dvd)
      hx' hy' with h|h|h|h|h|h
  · exact Or.inl (pair_lift x y 4 h)
  · exact Or.inr (Or.inl (pair_lift x y 8 h))
  · exact Or.inr (Or.inr (Or.inl (pair_lift x y 16 h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (pair_lift x y 32 h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (pair_lift x y 64 h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (pair_lift x y 128 h)))))

end Ribbon8
#print axioms Ribbon8.prime_to_small_class8
