import RibbonTwoVoltage
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Exponent

namespace RibbonTwo
open HaarVoltage HaarVoltageLift HaarTwoKernel
variable {G H : Type*} [Group G] [Group H]

/-- Repeat the quotient's chosen port sequence until its kernel voltage
returns to 1. Simplicity follows from the quotient phase and the powers
of that single voltage. -/
theorem lift_cycle (f : G→*H) (x y : G) {r m : ℕ} (two : BoundedTwo f m)
    (base : Ribbon.Cycle (f x) (f y) (2^r)) :
    ∃ j ≤ m, Ribbon.Cycle x y (2^(r+j)) := by
  classical
  have hpos : 0 < 2^r := by positivity
  letI : NeZero (2^r) := ⟨ne_of_gt hpos⟩
  obtain ⟨B,inj,edges⟩ := base
  have hb (i : Fin (2^r)) : Ribbon.Adj (f x) (f y) (B i) (B (i+1)) := by
    have hi : (⟨(i.val+1)%(2^r),Nat.mod_lt _ hpos⟩ : Fin (2^r)) = i+1 :=
      (index_succ (2^r) i.val).trans (by rw [val_index])
    simpa only [hi] using edges i
  choose L hL using fun i => RibbonTwo.labeled_of_adj f x y (B i) (B (i+1)) (hb i)
  have mL := voltage_kernel f B L (fun i => (hL i).2)
  obtain ⟨j,hj,hord⟩ := order_power f two mL
  refine ⟨j,hj,?_⟩
  rw [pow_add]
  exact RibbonTwo.lift_labeled f x y B inj L (fun i => (hL i).1)
    (fun i => (hL i).2) _ (by positivity) hord

/-- The entire selected rim is a simple cycle of the generator's order. -/
theorem rim_order (x y : G) (side : Bool) {k : ℕ} (hk : 0<k)
    (ord : orderOf (if side then y else x)=k) : Ribbon.Cycle x y k := by
  let g := if side then y else x
  let v : Fin k→Bool×G := fun i => (side,g^i.val)
  refine ⟨v,?_,?_⟩
  · intro i j e
    apply Fin.ext
    have he := congrArg (Prod.snd : Bool×G→G) e
    exact pow_injOn_Iio_orderOf (by rw [ord]; exact i.isLt) (by rw [ord]; exact j.isLt) he
  · intro i
    have e : g^i.val*g=g^((i.val+1)%k) := by
      calc
        _ = g^(i.val+1) := (pow_succ _ _).symm
        _ = g^((i.val+1)%orderOf g) := (pow_mod_orderOf g _).symm
        _ = _ := congrArg (fun n : ℕ => g^((i.val+1)%n)) ord
    cases side
    · exact Or.inl ⟨rfl,rfl,Or.inl e⟩
    · exact Or.inr (Or.inl ⟨rfl,rfl,Or.inl e⟩)

theorem collapsed_rim (f : G→*H) (x y : G) (b : Bool)
    {m : ℕ} (two : BoundedTwo f m)
    (hf : f (if b then y else x)=1) (h : (if b then y else x)^2≠1) :
    ∃ j, 2≤j ∧ j≤m ∧ Ribbon.Cycle x y (2^j) := by
  obtain ⟨j,jm,e⟩ := order_power f two (show (if b then y else x)∈f.ker from hf)
  have low : 2≤j := by
    by_contra! n
    have div : orderOf (if b then y else x)∣2 := by
      rw [e]
      interval_cases j <;> decide
    exact h (orderOf_dvd_iff_pow_eq_one.mp div)
  exact ⟨j,low,jm,rim_order x y b (by positivity) e⟩

/-- A dyadic cycle bound under any 2-bounded homomorphism. The two
rim generators are assumed to have order at least three. -/
theorem bound_via_hom (f : G→*H) (x y : G) {m b : ℕ} (two : BoundedTwo f m)
    (hx : x^2≠1) (hy : y^2≠1)
    (base : f x≠1 → f y≠1 → ∃ r, 2≤r ∧ r≤b ∧ Ribbon.Cycle (f x) (f y) (2^r)) :
    ∃ r, 2≤r ∧ r≤b+m ∧ Ribbon.Cycle x y (2^r) := by
  by_cases gx : f x=1
  · obtain ⟨r,l,up,C⟩ := collapsed_rim f x y false two gx hx
    exact ⟨r,l,by omega,C⟩
  by_cases gy : f y=1
  · obtain ⟨r,l,up,C⟩ := collapsed_rim f x y true two gy hy
    exact ⟨r,l,by omega,C⟩
  obtain ⟨r,l,up,C⟩ := base gx gy
  obtain ⟨j,jm,lifted⟩ := RibbonTwo.lift_cycle f x y two C
  exact ⟨r+j,by omega,by omega,lifted⟩

theorem exponent_two_power (N : Subgroup G) [Finite N] (two : IsPGroup 2 N) :
    ∃ m : ℕ, Monoid.exponent N=2^m := by
  obtain ⟨n,h⟩ := isPGroup_iff_exponent_dvd_pow.mp two
  obtain ⟨m,_,eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
  exact ⟨m,eq⟩

theorem quotient_bound (N : Subgroup G) [N.Normal] [Finite N]
    (two : IsPGroup 2 N) (x y : G) (b : ℕ) (hx : x^2≠1) (hy : y^2≠1)
    (base : (QuotientGroup.mk' N) x≠1 → (QuotientGroup.mk' N) y≠1 →
      ∃ r, 2≤r ∧ r≤b ∧ Ribbon.Cycle ((QuotientGroup.mk' N) x) ((QuotientGroup.mk' N) y) (2^r)) :
    ∃ r, 2≤r ∧ 2^r≤2^b * Monoid.exponent N ∧ Ribbon.Cycle x y (2^r) := by
  obtain ⟨m,hm⟩ := exponent_two_power N two
  have h : BoundedTwo (QuotientGroup.mk' N) m := by
    intro a ha
    rw [QuotientGroup.ker_mk'] at ha
    rw [←hm]
    exact Subgroup.pow_exponent_eq_one ha
  obtain ⟨r,rl,ru,cyc⟩ := bound_via_hom (QuotientGroup.mk' N) x y h hx hy base
  refine ⟨r,rl,?_,cyc⟩
  rw [hm,←pow_add]
  exact Nat.pow_le_pow_right (by decide) ru

end RibbonTwo
#print axioms RibbonTwo.lift_cycle
#print axioms RibbonTwo.quotient_bound
