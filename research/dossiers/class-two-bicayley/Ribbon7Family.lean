import Ribbon7Exceptional

namespace Ribbon7
open HaarClass4Structure HaarClass4Generate HaarClass4Ports RibbonClass4Fallback
open scoped commutatorElement
variable {G : Type*} [Group G]

private theorem comm_if_projected_trivial (nil : LS G 7=⊥) (x y : G)
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
  have all := d.trans (d₂.trans (d₃.trans (d₄.trans (d₅.trans (d₆.trans nil)))))
  have hC := layer_c x y
  rw [all,Subgroup.mem_bot] at hC
  exact hC

private theorem generated_bound (nil : LS G 7=⊥) (x y : G) (gen : Generates x y)
    (odd : Odd (Nat.card G)) (no3 : ¬3 ∣ Nat.card G) (hx : x≠1) (hy : y≠1)
    (ex : Z x y ≠ 1 → exceptional x y) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨
      Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 ∨ Ribbon.Cycle x y 128 := by
  by_cases C : portC x y ∈ LS G 2
  · have h := comm_if_projected_trivial nil x y gen C
    have z : Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 :=
      Ribbon.class2_pair x y (portC x y) (h ▸ Commute.one_left x) (h ▸ Commute.one_left y)
        (ports_xy x y) hx (by simpa only [pow_two] using HaarClass3Odd.odd_no_involution odd hy)
    exact z.imp_right (fun z => z.imp_right Or.inl)
  · have D : (QuotientGroup.mk' (LS G 2) (portC x y))≠1 :=
      fun e => C ((QuotientGroup.eq_one_iff _).mp e)
    have O := HaarClass3Separation64.odd_projection odd
    have Q : ¬3 ∣ Nat.card (G ⧸ LS G 2) :=
      fun t => no3 (dvd_trans t (LS G 2).card_quotient_dvd_card)
    have R := RibbonClass4.root_good_card O Q D
    have good (k : Nat) (a : 1≤k) (b : k≤4) :
        (QuotientGroup.mk' (LS G 2) (portC x y))^k ≠ 1 := by
      interval_cases k
      · simpa only [pow_one] using R.1
      · exact R.2.1
      · exact R.2.2
      · intro eq
        apply HaarClass3Odd.odd_no_involution O R.2.1
        rwa [← pow_mul]
    exact Or.inr (Or.inr (Or.inr (local_bound_if nil x y good ex)))

theorem odd_not_three_class7 [Finite G] (nil : LS G 7=⊥) (x y : G)
    (odd : Odd (Nat.card G)) (no3 : ¬3 ∣ Nat.card G) (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨
      Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 ∨ Ribbon.Cycle x y 128 := by
  let S := Pair x y
  have dvd : Nat.card S ∣ Nat.card G := S.card_subgroup_dvd_card
  have hx' : leftPort x y≠1 := fun e => hx (congrArg Subtype.val e)
  have hy' : rightPort x y≠1 := fun e => hy (congrArg Subtype.val e)
  rcases generated_bound (pair_nil x y 7 nil) _ _ (pair_generates x y)
      (Odd.of_dvd_nat odd dvd) (fun t => no3 (dvd_trans t dvd)) hx' hy' (exceptional_proved (pair_nil x y 7 nil) _ _) with h|h|h|h|h|h
  · exact Or.inl (pair_lift x y 4 h)
  · exact Or.inr (Or.inl (pair_lift x y 8 h))
  · exact Or.inr (Or.inr (Or.inl (pair_lift x y 16 h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (pair_lift x y 32 h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (pair_lift x y 64 h)))))

  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (pair_lift x y 128 h)))))
end Ribbon7
#print axioms Ribbon7.odd_not_three_class7
