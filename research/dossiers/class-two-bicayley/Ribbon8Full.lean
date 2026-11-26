import Ribbon8Family
import Ribbon8SmallFamily
namespace Ribbon8
open HaarClass4Structure HaarClass4Generate HaarClass4Ports RibbonClass4Fallback HaarUniversal36
open scoped commutatorElement
variable {G : Type*} [Group G]

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

private theorem generated_odd_not_three [Finite G] (nil : LS G 8=⊥) (x y : G)
    (gen : Generates x y) (odd : Odd (Nat.card G)) (no3 : ¬3 ∣ Nat.card G)
    (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨
      Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 ∨ Ribbon.Cycle x y 128 := by
  have hy2 := HaarClass3Odd.odd_no_involution odd hy
  let C := (QuotientGroup.mk' (LS G 2) (portC x y))
  by_cases c1 : C=1
  · have c := comm_if_projected_trivial nil x y gen ((QuotientGroup.eq_one_iff _).mp c1)
    have z : Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 :=
      Ribbon.class2_pair x y (portC x y) (c ▸ Commute.one_left x) (c ▸ Commute.one_left y)
        (ports_xy x y) hx (by simpa only [pow_two] using hy2)
    exact z.imp_right (fun z => z.imp_right Or.inl)
  · by_cases o5 : orderOf C=5
    · exact Ribbon8Small.projected_order_5_or_7 nil 0 x y gen hx
        (by simpa only [pow_two] using hy2) o5
    by_cases o7 : orderOf C=7
    · exact Ribbon8Small.projected_order_5_or_7 nil 1 x y gen hx
        (by simpa only [pow_two] using hy2) o7
    have good (k : Nat) (lo : 1≤k) (hi : k≤7) : C^k≠1 := by
      intro E
      have d := orderOf_dvd_iff_pow_eq_one.mpr E
      have le := (Nat.le_of_dvd (by omega : 0<k) d).trans hi
      have D : orderOf C ∣ Nat.card G := dvd_trans (orderOf_dvd_natCard C) (LS G 2).card_quotient_dvd_card
      have O := Odd.of_dvd_nat odd D
      have small : orderOf C=1 ∨ orderOf C=3 ∨ orderOf C=5 ∨ orderOf C=7 := by
        obtain ⟨v,h⟩ := O
        omega
      rcases small with H|H|H|H
      · exact c1 (orderOf_eq_one_iff.mp H)
      · exact no3 (H ▸ D)
      · exact o5 H
      · exact o7 H
    exact Or.inr (Or.inr (Or.inr (local_bound nil x y good)))

theorem odd_not_three_class8 [Finite G] (nil : LS G 8=⊥) (x y : G)
    (odd : Odd (Nat.card G)) (no3 : ¬3 ∣ Nat.card G) (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨
      Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 ∨ Ribbon.Cycle x y 128 := by
  let S := Pair x y
  have dvd : Nat.card S ∣ Nat.card G := S.card_subgroup_dvd_card
  have hx' : leftPort x y≠1 := fun e => hx (congrArg Subtype.val e)
  have hy' : rightPort x y≠1 := fun e => hy (congrArg Subtype.val e)
  rcases generated_odd_not_three (pair_nil x y 8 nil) _ _ (pair_generates x y)
      (Odd.of_dvd_nat odd dvd) (fun t => no3 (dvd_trans t dvd)) hx' hy' with h|h|h|h|h|h
  · exact Or.inl (pair_lift x y 4 h)
  · exact Or.inr (Or.inl (pair_lift x y 8 h))
  · exact Or.inr (Or.inr (Or.inl (pair_lift x y 16 h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (pair_lift x y 32 h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (pair_lift x y 64 h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (pair_lift x y 128 h)))))

end Ribbon8
#print axioms Ribbon8.odd_not_three_class8
