import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp

open scoped BigOperators
namespace CatalogAlteration

variable {J T : Type*}

noncomputable def inverseTotal (clusters : Finset J) (p : J → ℝ) : ℝ :=
  ∑ j ∈ clusters, (p j)⁻¹

noncomputable def equitable (clusters : Finset J) (p : J → ℝ) (j : J) : ℝ :=
  (p j)⁻¹ / inverseTotal clusters p

theorem inverse_total_pos (clusters : Finset J) (p : J → ℝ)
    (ne : clusters.Nonempty) (pos : ∀ j ∈ clusters, 0 < p j) :
    0 < inverseTotal clusters p := by
  unfold inverseTotal
  obtain ⟨j,hj⟩ := ne
  exact Finset.sum_pos' (fun i hi => (inv_pos.mpr (pos i hi)).le)
    ⟨j,hj,inv_pos.mpr (pos j hj)⟩

theorem equitable_normalizes (clusters : Finset J) (p : J → ℝ)
    (ne : clusters.Nonempty) (pos : ∀ j ∈ clusters, 0 < p j) :
    (∑ j ∈ clusters, equitable clusters p j)=1 := by
  unfold equitable
  simp_rw [div_eq_mul_inv]
  rw [←Finset.sum_mul]
  change inverseTotal clusters p * (inverseTotal clusters p)⁻¹ = 1
  exact mul_inv_cancel₀ (inverse_total_pos clusters p ne pos).ne'

theorem equitable_cancel (clusters : Finset J) (p : J → ℝ)
    (j : J) (pos : 0 < p j) :
    equitable clusters p j * p j = (inverseTotal clusters p)⁻¹ := by
  unfold equitable
  rw [div_eq_mul_inv, mul_right_comm, inv_mul_cancel₀ pos.ne', one_mul]

/-- The distribution equalizes the transcript-retention factor for
any transcript-specific canonical cluster. -/
theorem equitable_thinning (clusters : Finset J) (p : J → ℝ)
    (pos : ∀ j ∈ clusters, 0 < p j)
    (accept : Finset T) (chosen : T → J) (inJ : ∀ t ∈ accept, chosen t∈clusters)
    (mass : T → ℝ) :
    ∑ t ∈ accept, mass t*(equitable clusters p (chosen t)*p (chosen t)) =
      (∑ t∈accept,mass t) * (inverseTotal clusters p)⁻¹ := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [equitable_cancel clusters p (chosen t) (pos _ (inJ t ht))]

/-- Within a fixed layout and uniform local supports, the smallest
retention factor cannot exceed the equalized one, for any distribution. -/
theorem equitable_maximin (clusters : Finset J) (p q : J → ℝ) (value : ℝ)
    (ne : clusters.Nonempty) (pos : ∀ j ∈ clusters, 0 < p j)
    (prob : ∑ j ∈ clusters,q j=1)
    (retention : ∀ j ∈ clusters, value ≤ q j*p j) :
    value ≤ (inverseTotal clusters p)⁻¹ := by
  have ht := inverse_total_pos clusters p ne pos
  have bound (j : J) (h : j∈clusters) : value/(p j) ≤ q j :=
    (div_le_iff₀ (pos j h)).mpr (retention j h)
  have b := Finset.sum_le_sum bound
  simp_rw [div_eq_mul_inv] at b
  rw [←Finset.mul_sum,prob] at b
  change value * inverseTotal clusters p ≤ 1 at b
  exact (le_div_iff₀ ht).2 b |>.trans_eq (one_div _)

/-- Water-filling lower certificate. If each survival curve has a
supporting line of negative slope p at its equalized exposure, then
inverse-slope weights certify the common survival lower bound against
every exposure vector of at most that total size. -/
theorem slope_balance_lower (clusters : Finset J) (p target exposed pay : J → ℝ)
    (ne : clusters.Nonempty) (pos : ∀ j ∈ clusters, 0 < p j) (level : ℝ)
    (budget : (∑ j ∈ clusters, exposed j) ≤ ∑ j ∈ clusters,target j)
    (support : ∀ j ∈ clusters, level+p j*(target j-exposed j) ≤ pay j) :
    level ≤ ∑ j ∈ clusters, equitable clusters p j*pay j := by
  have invpos := (inv_pos.mpr (inverse_total_pos clusters p ne pos)).le
  have qi (j : J) (h : j∈clusters) : 0 ≤ equitable clusters p j :=
    div_nonneg (inv_pos.mpr (pos j h)).le (inverse_total_pos clusters p ne pos).le
  have ho := Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (support j hj) (qi j hj)
  have e (j : J) (hj : j∈clusters) :
      equitable clusters p j*(level+p j*(target j-exposed j)) =
      (equitable clusters p j)*level + (inverseTotal clusters p)⁻¹*(target j-exposed j) := by
    rw [mul_add,←mul_assoc,equitable_cancel clusters p j (pos j hj)]
  rw [Finset.sum_congr rfl e,Finset.sum_add_distrib,←Finset.sum_mul,
      equitable_normalizes clusters p ne pos,one_mul,←Finset.mul_sum,Finset.sum_sub_distrib] at ho
  exact (le_add_of_nonneg_right (mul_nonneg invpos (sub_nonneg.mpr budget))).trans ho

/-- Upper certificate: a feasible distribution of integer exposure
vectors with every cluster's expected payoff equal to the level
dominates any independent choice of cluster probabilities. -/
theorem equal_expectation_upper
    (clusters : Finset J) (exposures : Finset T)
    (q : J → ℝ) (mass : T → ℝ) (pay : T → J → ℝ) (level : ℝ)
    (hq : (∑ j ∈ clusters,q j)=1)
    (hm : (∑ e ∈ exposures,mass e)=1)
    (pos : ∀ e ∈ exposures, 0 ≤ mass e)
    (equal : ∀ j ∈ clusters,(∑ e ∈ exposures,mass e*pay e j)=level) :
    ∃ e ∈ exposures, (∑ j ∈ clusters,q j*pay e j) ≤ level := by
  have avg : (∑ e ∈ exposures,mass e*(∑ j ∈ clusters,q j*pay e j))=level := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have eq (j : J) (hj : j∈clusters) :
        (∑ e ∈ exposures,mass e*(q j*pay e j))=q j*level := by
      rw [←equal j hj,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [mul_left_comm]
    rw [Finset.sum_congr rfl eq,←Finset.sum_mul,hq,one_mul]
  by_contra! bad
  have some : ∃ e ∈ exposures, 0<mass e := by
    by_contra! b
    have hh : (∑ e ∈ exposures,mass e) ≤ ∑ _e ∈ exposures,(0:ℝ) :=
      Finset.sum_le_sum b
    rw [hm] at hh
    simp at hh
    exact (not_le_of_gt zero_lt_one) hh
  obtain ⟨e,he,hval⟩ := some
  have h := Finset.sum_lt_sum (fun v hv => mul_le_mul_of_nonneg_left (bad v hv).le (pos v hv))
    ⟨e,he,mul_lt_mul_of_pos_left (bad e he) hval⟩
  rw [←Finset.sum_mul,hm,one_mul,avg] at h
  exact (lt_irrefl _) h

#print axioms equal_expectation_upper
#print axioms slope_balance_lower
#print axioms equitable_normalizes
#print axioms equitable_thinning
#print axioms equitable_maximin
end CatalogAlteration
