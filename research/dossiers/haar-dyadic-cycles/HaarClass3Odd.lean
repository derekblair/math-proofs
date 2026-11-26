import HaarCentral
import HaarClass3Cycle
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.OrderOfElement

namespace HaarClass3Odd
open HaarAllNoncommuting
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem odd_no_involution (odd : Odd (Nat.card G)) {z : G} (h₁ : z ≠ 1) :
    z^2 ≠ 1 := by
  intro eq
  have d := orderOf_dvd_iff_pow_eq_one.mpr eq
  rcases (Nat.dvd_prime Nat.prime_two).mp d with n | n
  · exact h₁ (orderOf_eq_one_iff.mp n)
  · have h := Odd.of_dvd_nat odd (orderOf_dvd_natCard z)
    rw [n] at h
    exact (by decide : ¬ Odd (2:ℕ)) h

theorem from_central_third (odd : Odd (Nat.card G)) (x y c u v : G)
    (r : x*y=y*x*c) (rx : c*x=x*c*u) (ry : c*y=y*c*v)
    (hu : ∀ z : G, Commute u z) (hv : ∀ z : G, Commute v z) (hn : v ≠ 1) :
    HasCycle x y 32 := by
  let P := Subgroup.center G
  let Q := QuotientGroup.mk' P
  have hu' : Q u=1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.mem_center_iff.mpr (fun z => (hu z).eq.symm)
  have hv' : Q v=1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.mem_center_iff.mpr (fun z => (hv z).eq.symm)
  have hc : Q c ≠ 1 := by
    intro he
    have mem : c ∈ P := (QuotientGroup.eq_one_iff _).mp he
    have e := Subgroup.mem_center_iff.mp mem y
    -- cancel the common left factor using the original centrality equation.
    have ee : y*c = (y*c)*v := (Subgroup.mem_center_iff.mp mem y).trans ry
    exact hn ((mul_left_cancel (a:=y*c) (by simpa using ee : (y*c)*1 = (y*c)*v)).symm)
  have qo := Odd.of_dvd_nat odd P.card_quotient_dvd_card
  exact HaarClass3Cycle.certified x y c u v hu hv r rx ry Q hc
    (odd_no_involution qo hc) hu' hv' hn (odd_no_involution odd hn)

theorem adj_flip {x y : G} {a b : Bool × G} :
    HaarCycle.haarAdj x y a b ↔ HaarCycle.haarAdj y x a b := by
  cases h : a.1 <;> simp only [HaarCycle.haarAdj,h,Bool.false_eq_true,ite_false,ite_true]
  all_goals tauto

theorem exists_of_central_third (odd : Odd (Nat.card G)) (x y c u v : G)
    (hx : x≠1) (hy : y≠1) (hxy : x≠y)
    (r : x*y=y*x*c) (rx : c*x=x*c*u) (ry : c*y=y*c*v)
    (hu : ∀ z : G, Commute u z) (hv : ∀ z : G, Commute v z) :
    HasCycle x y 4 ∨ HasCycle x y 8 ∨ HasCycle x y 16 ∨ HasCycle x y 32 := by
  by_cases hn : v=1
  · by_cases hm : u=1
    · have cx : Commute c x := by change c*x=x*c; simpa [hm] using rx
      have cy : Commute c y := by change c*y=y*c; simpa [hn] using ry
      rcases HaarCentral.dyadic_cycle x y c hx hy hxy cx cy r with h|h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · have rr : y*x=x*y*c⁻¹ := by rw [r,mul_assoc (y*x),mul_inv_cancel,mul_one]
      have ar : c⁻¹*y=y*c⁻¹*v⁻¹ := by
        simpa using HaarCycle.shift c y v (hv c) ry (-1)
      have br : c⁻¹*x=x*c⁻¹*u⁻¹ := by
        simpa using HaarCycle.shift c x u (hu c) rx (-1)
      obtain ⟨W,hi,ha⟩ := from_central_third odd y x c⁻¹ v⁻¹ u⁻¹ rr ar br
        (fun z => (hv z).inv_left) (fun z => (hu z).inv_left) (by simpa using hm)
      exact Or.inr (Or.inr (Or.inr ⟨W,hi,fun i => adj_flip.mpr (ha i)⟩))
  · exact Or.inr (Or.inr (Or.inr (from_central_third odd x y c u v r rx ry hu hv hn)))

def gamma3 (G : Type*) [Group G] : Subgroup G := ⁅commutator G, (⊤ : Subgroup G)⁆

theorem class_three (odd : Odd (Nat.card G))
    (class_le_three : ⁅gamma3 G, (⊤ : Subgroup G)⁆ = ⊥)
    (x y : G) (hx : x≠1) (hy : y≠1) (hxy : x≠y) :
    HasCycle x y 4 ∨ HasCycle x y 8 ∨ HasCycle x y 16 ∨ HasCycle x y 32 := by
  let c := ⁅x⁻¹,y⁻¹⁆
  let u := ⁅c,x⁆
  let v := ⁅c,y⁆
  have cent : gamma3 G ≤ Subgroup.center G :=
    Subgroup.commutator_top_right_eq_bot_iff_le_center.mp class_le_three
  have hc : c ∈ commutator G := by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hu : ∀ z : G, Commute u z := by
    intro z
    exact (Subgroup.mem_center_iff.mp (cent (Subgroup.commutator_mem_commutator hc (by simp))) z).symm
  have hv : ∀ z : G, Commute v z := by
    intro z
    exact (Subgroup.mem_center_iff.mp (cent (Subgroup.commutator_mem_commutator hc (by simp))) z).symm
  have r : x*y=y*x*c := by unfold c; simp only [commutatorElement_def,inv_inv]; group
  have rx : c*x=x*c*u := by
    rw [← (hu (x*c)).eq]
    unfold u
    simp only [commutatorElement_def]
    group
  have ry : c*y=y*c*v := by
    rw [← (hv (y*c)).eq]
    unfold v
    simp only [commutatorElement_def]
    group
  exact exists_of_central_third odd x y c u v hx hy hxy r rx ry hu hv

end HaarClass3Odd

#print axioms HaarClass3Odd.class_three
