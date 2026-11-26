import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

open Polynomial
open scoped BigOperators

namespace RepairSegments

variable {F : Type*} [Field F]

noncomputable def witness (sites : Finset F) : F[X] :=
  ∏ a ∈ sites, (1 - C a⁻¹ * X)

theorem witness_zero (sites : Finset F) : (witness sites).eval 0 = 1 := by
  simp [witness, Polynomial.eval_prod]

theorem witness_degree (sites : Finset F) : (witness sites).natDegree ≤ sites.card := by
  calc
    _ ≤ ∑ a ∈ sites, (1 - C a⁻¹ * X : F[X]).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _a ∈ sites, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro a _
      refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
      simpa using (Polynomial.natDegree_C_mul_X_pow_le (a⁻¹) 1)
    _ = _ := by simp

theorem witness_eval_iff (sites : Finset F) (a : F) (hs : ∀ x ∈ sites, x ≠ 0) :
    (witness sites).eval a = 0 ↔ a ∈ sites := by
  rw [witness, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨x,xin,h⟩
    have h' : 1 - x⁻¹ * a = 0 := by simpa using h
    have e : x⁻¹ * a = 1 := (sub_eq_zero.mp h').symm
    have := congrArg (fun z => x * z) e
    rw [← mul_assoc, mul_inv_cancel₀ (hs x xin), one_mul, mul_one] at this
    simpa [this] using xin
  · intro ha
    exact ⟨a,ha,by simp [inv_mul_cancel₀ (hs a ha)]⟩

theorem roots_capacity (sites : Finset F) (p : F[X]) (hp : p.eval 0=1)
    (hz : ∀ a ∈ sites, p.eval a=0) :
    sites.card ≤ p.natDegree := by
  have pn : p ≠ 0 := by
    intro h
    simp [h] at hp
  apply Polynomial.card_le_degree_of_subset_roots
  intro a ha
  exact (Polynomial.mem_roots pn).2 (hz a ha)

/-- Pairwise disjoint windows of candidate seams each demand a member of C.
Consequently a solution must have at least as many seams as greedy witnesses. -/
theorem disjoint_deficits_lower {k : ℕ} (W : Fin k → Set ℕ) (C : Finset ℕ)
    (disj : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hit : ∀ i, ∃ c ∈ C, c ∈ W i) :
    k ≤ C.card := by
  classical
  choose c cin win using hit
  let f : Fin k → ↥C := fun i => ⟨c i,cin i⟩
  have inj : Function.Injective f := by
    intro i j h
    by_contra ne
    have e : c i = c j := congrArg Subtype.val h
    exact Set.disjoint_left.mp (disj i j ne) (win i) (by rw [e]; exact win j)
  simpa using Fintype.card_le_of_injective f inj

theorem seam_direction (S T : Finset F) (a : F)
    (sn : ∀ x ∈ S, x ≠ 0) (tn : ∀ x ∈ T, x ≠ 0)
    (outside : a ∉ S) (inside : a ∈ T) :
    (witness T - witness S).eval 0 = 0 ∧ (witness T - witness S).eval a ≠ 0 := by
  refine ⟨by simp [witness_zero], ?_⟩
  simp only [Polynomial.eval_sub, (witness_eval_iff T a tn).mpr inside, zero_sub, neg_ne_zero]
  exact fun h => outside ((witness_eval_iff S a sn).mp h)

theorem greedy_deficits_lower {k : ℕ} (start stop : Fin k → ℕ) (C : Finset ℕ)
    (ordered : ∀ i j, i < j → stop i ≤ start j)
    (hit : ∀ i, ∃ c ∈ C, start i ≤ c ∧ c < stop i) :
    k ≤ C.card := by
  apply disjoint_deficits_lower (fun i => {c | start i ≤ c ∧ c < stop i}) C
  · intro i j ne
    refine Set.disjoint_left.mpr ?_
    intro c hi hj
    change start i ≤ c ∧ c < stop i at hi
    change start j ≤ c ∧ c < stop j at hj
    rcases lt_or_gt_of_ne ne with h | h
    · have p := ordered i j h
      omega
    · have p := ordered j i h
      omega
  · exact hit

#print axioms seam_direction
#print axioms greedy_deficits_lower
#print axioms witness_degree
#print axioms witness_eval_iff
#print axioms roots_capacity
#print axioms disjoint_deficits_lower
end RepairSegments
