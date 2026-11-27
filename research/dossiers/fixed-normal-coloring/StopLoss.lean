import Mathlib.Tactic

namespace FixedNormal

open scoped BigOperators

def hinge (t z : ℝ) : ℝ := max 0 (t - z)

theorem sum_hinge_filter {ι : Type*} (A : Finset ι) (f : ι → ℝ) (t : ℝ) :
    (∑ i ∈ A, hinge t (f i)) = ∑ i ∈ A.filter (fun i => f i < t), (t - f i) := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : f i < t
  · simp [h, hinge, max_eq_right (sub_nonneg.mpr h.le)]
  · simp [h, hinge, max_eq_left (sub_nonpos.mpr (not_lt.mp h))]

theorem sublevel_implies_stop_loss {ι κ : Type*}
    (A : Finset ι) (B : Finset κ) (f : ι → ℝ) (g : κ → ℝ)
    (hmatch : ∀ S ⊆ A, ∃ T ⊆ B, T.card = S.card ∧
      (∑ j ∈ T, g j) ≤ ∑ i ∈ S, f i) (t : ℝ) :
    (∑ i ∈ A, hinge t (f i)) ≤ ∑ j ∈ B, hinge t (g j) := by
  classical
  rw [sum_hinge_filter]
  let S := A.filter (fun i => f i < t)
  change (∑ i ∈ S, (t - f i)) ≤ _
  obtain ⟨T,hT,hcard,hcost⟩ := hmatch S (Finset.filter_subset _ _)
  calc
    (∑ i ∈ S, (t - f i)) ≤ ∑ j ∈ T, (t - g j) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
      linarith
    _ ≤ ∑ j ∈ T, hinge t (g j) :=
      Finset.sum_le_sum (fun j _ => le_max_right _ _)
    _ ≤ ∑ j ∈ B, hinge t (g j) :=
      Finset.sum_le_sum_of_subset_of_nonneg hT (fun j _ _ => le_max_left _ _)

theorem nonnegative_hinge_mixture {ι κ χ : Type*}
    (A : Finset ι) (B : Finset κ) (p : Finset χ) (f : ι → ℝ) (g : κ → ℝ)
    (threshold weight : χ → ℝ) (hw : ∀ k ∈ p, 0 ≤ weight k)
    (H : ∀ t, (∑ i ∈ A, hinge t (f i)) ≤ ∑ j ∈ B, hinge t (g j)) :
    (∑ k ∈ p, weight k * (∑ i ∈ A, hinge (threshold k) (f i))) ≤
      ∑ k ∈ p, weight k * (∑ j ∈ B, hinge (threshold k) (g j)) :=
  Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (H (threshold k)) (hw k hk)

end FixedNormal

#print axioms FixedNormal.sublevel_implies_stop_loss
