import Ribbon6Algebra
import Ribbon6Mates
namespace Ribbon6
open HaarClass4Structure HaarClass4Generate HaarClass4Ports RibbonClass4Fallback Ribbon5Bridge
open scoped commutatorElement
variable {G : Type*} [Group G]
theorem local_bound (nil : LS G 6=⊥) (x y : G)
    (good : ∀ k : Nat, 1≤k → k≤4 →
      (QuotientGroup.mk' (LS G 2) (portC x y))^k ≠ 1) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 := by
  let f := QuotientGroup.mk' (LS G 2)
  let C := f (portC x y)
  have U : f (portU x y)=1 := (QuotientGroup.eq_one_iff _).mpr (layer_u x y)
  have V : f (portV x y)=1 := (QuotientGroup.eq_one_iff _).mpr (layer_v x y)
  have cx : Commute C (f x) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [C, portU,map_commutatorElement] using U
  have cy : Commute C (f y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [C, portV,map_commutatorElement] using V
  have xy : f x*f y=f y*f x*C := by simpa only [C,map_mul] using congrArg f (ports_xy x y)
  let F : Bool×G → Bool × (G ⧸ LS G 2) := fun u => (u.1,f u.2)
  by_cases nz : residue x y=1
  · left
    apply cycle_from_at x y wa (by decide) (by rw [a_end,nz]; rfl)
    have tr := transported f x y wa ta C cx cy xy (by decide +kernel)
      (fun i hi => astep ⟨i,hi⟩)
    intro i j le E
    have e : vert (f x) (f y) C ta[i.val]! = vert (f x) (f y) C ta[j.val]! :=
      (tr i.val i.isLt.le).symm.trans ((congrArg F E).trans (tr j.val j.isLt.le))
    exact separates_low (f x) (f y) C cx cy xy good _ _ (achart i j le) e
  · right
    apply cycle_from_at x y wc (by decide) (close nil x y)
    have tr := transported f x y wc tc C cx cy xy (by decide +kernel)
      (fun i hi => cstep ⟨i,hi⟩)
    intro i j le E
    rcases cchart i j le with s|d
    · have e : vert (f x) (f y) C tc[i.val]! = vert (f x) (f y) C tc[j.val]! :=
        (tr i.val i.isLt.le).symm.trans ((congrArg F E).trans (tr j.val j.isLt.le))
      exact separates_low (f x) (f y) C cx cy xy good _ _ s e
    · exact mate_sep x y nz _ _ d E

private theorem comm_if_projected_trivial (nil : LS G 6=⊥) (x y : G)
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
  have all := d.trans (d₂.trans (d₃.trans (d₄.trans (d₅.trans nil))))
  have hC := layer_c x y
  rw [all,Subgroup.mem_bot] at hC
  exact hC

private theorem generated_bound (nil : LS G 6=⊥) (x y : G) (gen : Generates x y)
    (odd : Odd (Nat.card G)) (no3 : ¬3 ∣ Nat.card G) (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨
      Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 := by
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
    exact Or.inr (Or.inr (Or.inr (local_bound nil x y good)))

theorem odd_not_three_class6 [Finite G] (nil : LS G 6=⊥) (x y : G)
    (odd : Odd (Nat.card G)) (no3 : ¬3 ∣ Nat.card G) (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨
      Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 := by
  let S := Pair x y
  have dvd : Nat.card S ∣ Nat.card G := S.card_subgroup_dvd_card
  have hx' : leftPort x y≠1 := fun e => hx (congrArg Subtype.val e)
  have hy' : rightPort x y≠1 := fun e => hy (congrArg Subtype.val e)
  rcases generated_bound (pair_nil x y 6 nil) _ _ (pair_generates x y)
      (Odd.of_dvd_nat odd dvd) (fun t => no3 (dvd_trans t dvd)) hx' hy' with h|h|h|h|h
  · exact Or.inl (pair_lift x y 4 h)
  · exact Or.inr (Or.inl (pair_lift x y 8 h))
  · exact Or.inr (Or.inr (Or.inl (pair_lift x y 16 h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (pair_lift x y 32 h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (pair_lift x y 64 h))))

end Ribbon6
#print axioms Ribbon6.local_bound
#print axioms Ribbon6.odd_not_three_class6
