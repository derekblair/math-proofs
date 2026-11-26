import Ribbon6Algebra
import RibbonDerived3Algebra
import Ribbon6Mates
namespace RibbonStationary
open Ribbon6 RibbonDerived3 HaarClass4Structure HaarClass4Generate HaarClass4Ports RibbonClass4Fallback Ribbon5Bridge
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem commute (dnil : DLS G 2=⊥) (x y : G) :
    Commute (Ribbon6.residue x y) (Ribbon6.U x y) := by
  apply commutatorElement_eq_one_iff_commute.mp
  exact Subgroup.mem_bot.mp (dnil ▸ Subgroup.commutator_mem_commutator
    (residue_in_D2 x y) (Ribbon6.upper_U x y) : _ ∈ (⊥ : Subgroup G))

theorem close (dnil : DLS G 2=⊥) (x y : G) : pathAt x y wc 64 = pathAt x y wc 0 := by
  have E : Ribbon6.U x y*Ribbon6.V x y = Ribbon6.V x y*Ribbon6.U x y := by
    have H := (commute dnil x y).eq
    change Ribbon6.U x y*Ribbon6.V x y*Ribbon6.U x y=Ribbon6.U x y*(Ribbon6.U x y*Ribbon6.V x y) at H
    exact (mul_left_cancel (by simpa only [mul_assoc] using H)).symm
  rw [c_end,E,mul_inv_cancel]
  rfl

theorem local_bound (dnil : DLS G 2=⊥) (x y : G)
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
  by_cases nz : Ribbon6.residue x y=1
  · left
    apply cycle_from_at x y wa (by decide) (by rw [a_end,nz]; rfl)
    have tr := transported f x y wa ta C cx cy xy (by decide +kernel)
      (fun i hi => astep ⟨i,hi⟩)
    intro i j le E
    have e : vert (f x) (f y) C ta[i.val]! = vert (f x) (f y) C ta[j.val]! :=
      (tr i.val i.isLt.le).symm.trans ((congrArg F E).trans (tr j.val j.isLt.le))
    exact separates_low (f x) (f y) C cx cy xy good _ _ (achart i j le) e
  · right
    apply cycle_from_at x y wc (by decide) (close dnil x y)
    have tr := transported f x y wc tc C cx cy xy (by decide +kernel)
      (fun i hi => cstep ⟨i,hi⟩)
    intro i j le E
    rcases cchart i j le with s|d
    · have e : vert (f x) (f y) C tc[i.val]! = vert (f x) (f y) C tc[j.val]! :=
        (tr i.val i.isLt.le).symm.trans ((congrArg F E).trans (tr j.val j.isLt.le))
      exact separates_low (f x) (f y) C cx cy xy good _ _ s e
    · exact mate_sep x y nz _ _ d E

theorem nontrivial_projected [Finite G] (dnil : DLS G 2=⊥) (x y : G)
    (odd : Odd (Nat.card G)) (no3 : ¬3 ∣ Nat.card G)
    (C : (QuotientGroup.mk' (LS G 2) (portC x y))≠1) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 := by
  let c := QuotientGroup.mk' (LS G 2) (portC x y)
  apply local_bound dnil x y
  intro k h1 h4 E
  have d : orderOf c ∣ k := orderOf_dvd_iff_pow_eq_one.mpr E
  have le := (Nat.le_of_dvd (by omega : 0<k) d).trans h4
  have D : orderOf c ∣ Nat.card G := dvd_trans (orderOf_dvd_natCard c) (LS G 2).card_quotient_dvd_card
  obtain ⟨v,h⟩ := Odd.of_dvd_nat odd D
  have small : orderOf c=1 ∨ orderOf c=3 := by omega
  exact small.elim (fun h => C (orderOf_eq_one_iff.mp h)) (fun h => no3 (h ▸ D))

end RibbonStationary
#print axioms RibbonStationary.nontrivial_projected
