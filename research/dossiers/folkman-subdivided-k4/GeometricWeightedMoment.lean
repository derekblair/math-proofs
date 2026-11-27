import GeometricWeightedLinks

namespace RobustFolkman.GeometricGap
open Finset
variable {Ω V : Type*} [Fintype Ω] [DecidableEq V] [Fintype V]

/-- A finite weighted-tail estimate with a tunable truncation scale.
This avoids a square root when composing the moment and Markov bounds. -/
theorem mean_if_event_le_split (p f : Ω → ℝ) (ev : Ω → Prop) [DecidablePred ev]
    (p0 : ∀ ω, 0 ≤ p ω) {M : ℝ} (hM : 0 < M) :
    Moment.mean p (fun ω => if ev ω then f ω else 0) ≤
      (1/(2*M))*Moment.mean p (fun ω => f ω^2) +
        (M/2)*Moment.mean p (fun ω => if ev ω then 1 else 0) := by
  unfold Moment.mean
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  have h (ω : Ω) :
      (if ev ω then f ω else 0) ≤ (1/(2*M)) * f ω^2 + (M/2)*(if ev ω then 1 else 0) := by
    by_cases he : ev ω
    · simp only [if_pos he, mul_one]
      field_simp [ne_of_gt hM]
      nlinarith only [sq_nonneg (f ω - M)]
    · simp only [if_neg he, mul_zero, add_zero]
      positivity
  calc
    _ ≤ p ω * ((1/(2*M)) * f ω^2 + (M/2)*(if ev ω then 1 else 0)) :=
      mul_le_mul_of_nonneg_left (h ω) (p0 ω)
    _ = _ := by ring

theorem mean_badLinkWeight_split (p : Ω → ℝ) (g : Ω → EdgeGraph V) (B : Ω → Finset V)
    (p0 : ∀ ω, 0 ≤ p ω) {M : ℝ} (hM : 0 < M) :
    Moment.mean p (fun ω => badLinkWeight (g ω) (B ω)) ≤
      (1/(2*M))*∑ v, Moment.mean p (fun ω => linkTriangleCount (g ω) v ^ 2) +
        (M/2)*∑ v, Moment.mean p (fun ω => if v∈B ω then 1 else 0) := by
  classical
  have eq : Moment.mean p (fun ω => badLinkWeight (g ω) (B ω)) =
      ∑ v, Moment.mean p (fun ω => if v∈B ω then linkTriangleCount (g ω) v else 0) := by
    unfold Moment.mean
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ω _
    rw [←Finset.mul_sum]
    simp only [Finset.sum_ite_mem, Finset.univ_inter, badLinkWeight]
  rw [eq, Finset.mul_sum, Finset.mul_sum, ←Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun v _ => mean_if_event_le_split p
    (fun ω => linkTriangleCount (g ω) v) (fun ω => v∈B ω) p0 hM

#print axioms mean_badLinkWeight_split
end RobustFolkman.GeometricGap
