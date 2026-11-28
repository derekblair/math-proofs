import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

namespace BoxCore
open scoped BigOperators

/-- In the ambient-coordinate basis, one projected segment span is paid by
two monotone own-coordinate increments, not by k coordinates. -/
theorem clipped_coordinate_gap (u v u' v' : ℝ) (hu : u ≤ u') (hv : v ≤ v') :
    |(u'-v')-(u-v)| ≤ (u'-u)+(v'-v) := by
  apply abs_le.mpr
  constructor <;> linarith

/-- Disjoint progress subintervals on a monotone curve cost at most the span
of that one progress coordinate on the parent box. -/
theorem sum_progress_intervals (lo hi : ℕ → ℝ) (a : ℝ)
    (_hlocal : ∀ i, lo i ≤ hi i) (hnext : ∀ i, hi i ≤ lo (i+1))
    (hstart : a ≤ lo 0) :
    ∀ n, (∑ i ∈ Finset.range (n+1), (hi i - lo i)) ≤ hi n-a := by
  intro n
  induction n with
  | zero => simp; linarith
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h := hnext n
    linarith

/-- Partition-boundary arcs can be charged to active current faces only.
A geometric proof supplies the set of ancestor-cut hits and the cover. -/
theorem active_face_budget {F E : Type*} [DecidableEq E]
    (faces : Finset F) (hits : F → Finset E) (crossing : Finset E) (k : ℕ)
    (number : faces.card ≤ 2*(k-1))
    (cap : ∀ f ∈ faces, (hits f).card ≤ 9*k)
    (cover : crossing ⊆ faces.biUnion hits) :
    crossing.card ≤ 18*k*(k-1) := by
  calc
    crossing.card ≤ (faces.biUnion hits).card := Finset.card_le_card cover
    _ ≤ ∑ f ∈ faces, (hits f).card := Finset.card_biUnion_le
    _ ≤ ∑ _f ∈ faces, 9*k := Finset.sum_le_sum fun f hf => cap f hf
    _ = faces.card * (9*k) := by simp
    _ ≤ (2*(k-1))*(9*k) := Nat.mul_le_mul_right _ number
    _ = 18*k*(k-1) := by
      rw [Nat.mul_right_comm 2 (k-1) (9*k), ← Nat.mul_assoc 2 9 k]

/-- Averaging over the finitely many open subintervals determined by
projection endpoints and forbidden vertex coordinates. -/
theorem good_subinterval {I : Type*} (S : Finset I) (len : I → ℝ)
    (hits : I → ℕ) (bound : ℕ) (hlen : ∀ i ∈ S, 0 ≤ len i)
    (hs : 0 < ∑ i ∈ S, len i)
    (avg : (∑ i ∈ S, (hits i : ℝ) * len i) ≤ (bound : ℝ) * ∑ i ∈ S, len i) :
    ∃ i ∈ S, hits i ≤ bound := by
  by_contra! h
  have hh : ∀ i ∈ S, (bound : ℝ)+1 ≤ (hits i : ℝ) := by
    intro i hi
    exact_mod_cast Nat.succ_le_of_lt (h i hi)
  have H : (∑ i ∈ S, ((bound : ℝ)+1) * len i) ≤
      ∑ i ∈ S, (hits i : ℝ) * len i :=
    Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hh i hi) (hlen i hi)
  rw [← Finset.mul_sum] at H
  rw [add_mul,one_mul] at H
  linarith

#print axioms clipped_coordinate_gap
#print axioms sum_progress_intervals
#print axioms active_face_budget
#print axioms good_subinterval
end BoxCore
