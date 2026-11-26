import RibbonD3Stationary
import RibbonOrder3Affine
import RibbonDerived3Small

namespace RibbonD3Stationary
open RibbonDerived3 RibbonP11 RibbonAffine HaarClass4Structure HaarClass4Generate HaarClass4Ports Ribbon8Small
open scoped commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G]
set_option maxHeartbeats 1000000

theorem stable_from_next (x y : G) (gen : Generates x y)
    (u : portU x y∈LS G 3) (v : portV x y∈LS G 3) : LS G 2=LS G 3 := by
  let S := LS G 3
  let f := QuotientGroup.mk' S
  have du : f (portU x y)=1 := (QuotientGroup.eq_one_iff _).mpr u
  have dv : f (portV x y)=1 := (QuotientGroup.eq_one_iff _).mpr v
  have X : Commute (f (portC x y)) (f x) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa [portU,map_commutatorElement] using du
  have Y : Commute (f (portC x y)) (f y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa [portV,map_commutatorElement] using dv
  have g := map_gen f (QuotientGroup.mk'_surjective S) gen
  have xy : f x*f y=f y*f x*f (portC x y) := by simpa using congrArg f (ports_xy x y)
  have h := c_center_class_two (f x) (f y) (f (portC x y)) g xy (gen_center _ _ _ g X Y)
  have M := map_ls f (QuotientGroup.mk'_surjective S) 2
  rw [h,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at M
  exact le_antisymm M (Subgroup.lowerCentralSeries_antitone ⊤ (by decide : 2≤3))

def MixedSmallCover : Prop :=
  ∀ {G K : Type u} [Group G] [Field K] [Finite G] [Finite K]
      (dnil : DLS G 3=⊥) (x y : G) (p : Fin 2) (μ : G→*Kˣ) (τ : G→K),
    orderOf (QuotientGroup.mk' (LS G 2) (portC x y))=prime p →
    (2:K)≠0 → Odd (Nat.card G) → RibbonP11.IsCocycle μ τ →
    RibbonP11.Normalized (RingHom.id K) x y μ τ →
    (μ x)^(Nat.card G)=1 → (μ y)^(Nat.card G)=1 → LongGood x y

theorem class_two_case (nil : LS G 2=⊥) (x y : G) (odd : Odd (Nat.card G))
    (hx : x≠1) (hy : y≠1) : LongGood x y := by
  have u := layer_u x y
  have v := layer_v x y
  rw [nil,Subgroup.mem_bot] at u v
  have h := Ribbon.class2_pair x y (portC x y) (commutatorElement_eq_one_iff_commute.mp u)
    (commutatorElement_eq_one_iff_commute.mp v) (ports_xy x y) hx
    (by simpa only [pow_two] using HaarClass3Odd.odd_no_involution odd hy)
  rcases h with h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

theorem small_dispatch (mix : MixedSmallCover.{u}) (dnil : DLS G 3=⊥)
    (x y : G) (p : Fin 2) (gen : Generates x y) (odd : Odd (Nat.card G))
    (hx : x≠1) (hy : y≠1)
    (order : orderOf (QuotientGroup.mk' (LS G 2) (portC x y))=prime p) :
    LongGood x y := by
  by_contra b
  have h32 : ¬Ribbon.Cycle x y 32 := fun h => b (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have h64 : ¬Ribbon.Cycle x y 64 := fun h => b (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  have h128 : ¬Ribbon.Cycle x y 128 := fun h => b (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  let f := QuotientGroup.mk' (LS G 2)
  have mem : (portC x y)^(prime p)∈LS G 2 := by
    apply (QuotientGroup.eq_one_iff _).mp
    change f ((portC x y)^(prime p))=1
    rw [map_pow,←order,pow_orderOf_eq_one]
  obtain ⟨u,v⟩ := project_both p x y mem (absence_forces dnil p x y order h32 h64 h128)
  have e := stable_from_next x y gen u v
  by_cases z : LS G 2=⊥
  · exact b (class_two_case z x y odd hx hy)
  have h : ¬LS G 2≤(commutator (D G)).map (D G).subtype := by
    have H := RibbonIA.stable_visible (G:=G) ⟨3,dnil⟩ e z
    rw [←Subgroup.top_lowerCentralSeries_one,Subgroup.top_subtype_lowerCentralSeries]
    exact H
  obtain ⟨K,F,I,μ,τ,two,co,n,px,py⟩ :=
    RibbonOrder3.stable_third_affine_of_visible x y gen odd e h
  exact b (mix dnil x y p μ τ order two odd co n px py)

theorem nonstationary_cover (mix : MixedSmallCover.{u}) : NonStationaryCover.{u} := by
  intro G _ _ dnil x y gen odd no3 hx hy nst
  let c := QuotientGroup.mk' (LS G 2) (portC x y)
  by_cases h5 : orderOf c=5
  · exact small_dispatch mix dnil x y 0 gen odd hx hy h5
  by_cases h7 : orderOf c=7
  · exact small_dispatch mix dnil x y 1 gen odd hx hy h7
  have c1 : c≠1 := fun h => nst ((QuotientGroup.eq_one_iff _).mp h)
  have good (k : Nat) (lo : 1≤k) (hi : k≤7) : c^k≠1 := by
    intro E
    have d := orderOf_dvd_iff_pow_eq_one.mpr E
    have le := (Nat.le_of_dvd (by omega : 0<k) d).trans hi
    have D : orderOf c ∣ Nat.card G := dvd_trans (orderOf_dvd_natCard c) (LS G 2).card_quotient_dvd_card
    have O := Odd.of_dvd_nat odd D
    have small : orderOf c=1 ∨ orderOf c=3 ∨ orderOf c=5 ∨ orderOf c=7 := by
      obtain ⟨v,h⟩ := O
      omega
    rcases small with H|H|H|H
    · exact c1 (orderOf_eq_one_iff.mp H)
    · exact no3 (H ▸ D)
    · exact h5 H
    · exact h7 H
  exact Or.inr (Or.inr (Or.inr (RibbonDerived3.local_bound dnil x y good)))

end RibbonD3Stationary
#print axioms RibbonD3Stationary.nonstationary_cover
