import HaarVoltageLift
import Mathlib.Data.Nat.Prime.Basic

namespace HaarTwoKernel
open HaarCycle HaarAllNoncommuting HaarVoltage HaarVoltageLift

variable {G H : Type*} [Group G] [Group H]

def BoundedTwo (φ : G →* H) (m : ℕ) : Prop :=
  ∀ g ∈ φ.ker, g^(2^m : ℕ) = 1

theorem card_two_bound (φ : G →* H) (m : ℕ)
    (h : Nat.card φ.ker ∣ 2^m) : BoundedTwo φ m := by
  intro g hg
  have e := orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard (⟨g,hg⟩ : φ.ker)).trans h)
  exact congrArg (fun x : φ.ker => x.val) e

theorem order_power (φ : G →* H) {m : ℕ} (two : BoundedTwo φ m)
    {g : G} (hg : g ∈ φ.ker) :
    ∃ j ≤ m, orderOf g = 2^j :=
  (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_iff_pow_eq_one.mpr (two g hg))

theorem lift_cycle (φ : G →* H) (x y : G) {r m : ℕ} (two : BoundedTwo φ m)
    (h : HasCycle (φ x) (φ y) (2^r)) :
    ∃ j ≤ m, HasCycle x y (2^(r+j)) := by
  classical
  have kp : 0 < 2^r := by positivity
  have : NeZero (2^r) := ⟨Nat.ne_of_gt kp⟩
  obtain ⟨B,inj,base⟩ := h
  have hb (i : Fin (2^r)) : haarAdj (φ x) (φ y) (B i) (B (i+1)) := by
    have hi : (⟨(i.val+1)%(2^r),Nat.mod_lt _ kp⟩ : Fin (2^r)) = i+1 := by
      exact (index_succ (2^r) i.val).trans (by rw [val_index])
    simpa only [hi] using base i
  choose s hs using fun i => labeled_of_adj φ x y (B i) (B (i+1)) (hb i)
  let L : Fin (2^r) → G := fun i => stepLabel (B i).1 (s i)
  have hg := voltage_kernel φ B L (fun i => (hs i).2.2)
  obtain ⟨j,hj,horder⟩ := order_power φ two hg
  refine ⟨j,hj,?_⟩
  rw [pow_add]
  exact lift_labeled φ x y B inj s (fun i => (hs i).1) (fun i => (hs i).2.1)
    (fun i => (hs i).2.2) _ (by positivity) horder

theorem incl_left (x y : G) (a b : Bool × G)
    (h : haarAdj 1 x a b) : haarAdj x y a b := by
  cases e : a.1 <;> simp [haarAdj,e] at h ⊢ <;> tauto

theorem incl_right (x y : G) (a b : Bool × G)
    (h : haarAdj 1 y a b) : haarAdj x y a b := by
  cases e : a.1 <;> simp [haarAdj,e] at h ⊢ <;> tauto

theorem collapsed_pair (φ : G →* H) (x y : G) {m : ℕ} (two : BoundedTwo φ m)
    (xy : x ≠ y) (he : φ x = φ y) :
    ∃ j, 2 ≤ j ∧ j ≤ 1+m ∧ HasCycle x y (2^j) := by
  have hg : HaarAllNoncommuting.h x y ∈ φ.ker := by
    change φ (x⁻¹*y)=1
    simp [he]
  obtain ⟨j,jm,oj⟩ := order_power φ two hg
  have jp : 0 < j := by
    by_contra! j0
    have jz : j=0 := by omega
    have bad : HaarAllNoncommuting.h x y = 1 :=
      orderOf_eq_one_iff.mp (by simpa [jz] using oj)
    exact xy (by simpa [HaarAllNoncommuting.h,inv_mul_eq_one] using bad)
  have gt : 1 < 2^j := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (Nat.ne_of_gt jp)
  have : NeZero (2*(2^j)) := ⟨by positivity⟩
  obtain ⟨V,vi,va⟩ := alternate x y (2^j) oj gt
  refine ⟨1+j,by omega,by omega,?_⟩
  rw [pow_add,pow_one]
  exact cycle_form V vi va

theorem overall (φ : G →* H) (x y : G) {m : ℕ} (two : BoundedTwo φ m)
    (odd : Odd (Nat.card H)) (cl : ⁅HaarClass3Odd.gamma3 H, (⊤ : Subgroup H)⁆ = ⊥)
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
  have d := HaarClass3Odd.class_three odd cl (φ x) (φ y) h1 h2 h3
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

end HaarTwoKernel

#print axioms HaarTwoKernel.overall
