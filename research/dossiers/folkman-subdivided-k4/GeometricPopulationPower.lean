import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace RobustFolkman.GeometricGap
open Filter
open scoped Topology InnerProductSpace

/-- A log-convex nonnegative sequence cannot grow asymptotically
slower than its first-step ratio. -/
theorem first_step_of_log_convex (u : ℕ→ℝ) (ρ C : ℝ) (ρ0 : 0≤ρ)
    (u0 : 0<u 0) (cv : ∀ n, (u (n+1))^2≤u n*u (n+2))
    (upper : ∀ n, u n≤C*ρ^n) : u 1≤ρ*u 0 := by
  by_contra! bad
  let b := u 1/u 0
  have bρ : ρ<b := (lt_div_iff₀ u0).2 bad
  have bp : 0<b := ρ0.trans_lt bρ
  have low (n : ℕ) : 0<u n ∧ b*u n≤u (n+1) := by
    induction n with
    | zero =>
      exact ⟨u0,(div_mul_cancel₀ _ u0.ne').le⟩
    | succ n ih =>
      obtain ⟨np,rat⟩ := ih
      have pos : 0<u (n+1) := (mul_pos bp np).trans_le rat
      refine ⟨pos,(le_of_mul_le_mul_right ?_ np)⟩
      have z := mul_le_mul_of_nonneg_right rat pos.le
      have h := cv n
      nlinarith only [z,h]
  have emp (n : ℕ) : b^n*u 0≤u n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      have s := mul_le_mul_of_nonneg_left ih bp.le
      have h := (low n).2
      nlinarith only [s,h]
  have ht : Tendsto (fun n : ℕ => C*(ρ/b)^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg ρ0 bp.le)
      ((div_lt_one₀ bp).2 bρ)).const_mul C
  obtain ⟨n,hn⟩ := (ht.eventually (gt_mem_nhds u0)).exists
  have h := (emp n).trans (upper n)
  rw [div_pow] at hn
  have z : C*(ρ^n/b^n)=(C*ρ^n)/(b^n) := by ring
  rw [z] at hn
  have hh := (div_lt_iff₀ (pow_pos bp n)).1 hn
  nlinarith only [h,hh]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def linearOrbit (T : E →ₗ[ℝ] E) (f : E) : ℕ→E
  | 0 => f
  | n+1 => T (linearOrbit T f n)

theorem symmetric_orbit_log_convex (T : E→ₗ[ℝ] E) (hs : T.IsSymmetric) (f : E) (n : ℕ) :
    ‖linearOrbit T f (n+1)‖^2≤‖linearOrbit T f n‖*‖linearOrbit T f (n+2)‖ := by
  let u := linearOrbit T f n
  change ‖T u‖^2 ≤ ‖u‖*‖T (T u)‖
  rw [←real_inner_self_eq_norm_sq,hs u (T u)]
  exact real_inner_le_norm _ _

/-- The self-adjoint Markov operator estimate reduces to an exponential
bound on the iterates of each bounded Lipschitz test vector. -/
theorem symmetric_first_step_from_power (T : E→ₗ[ℝ] E) (hs : T.IsSymmetric)
    (ρ : ℝ) (ρ0 : 0≤ρ) (f : E)
    (bound : ∃ C : ℝ, ∀ n, ‖linearOrbit T f n‖≤C*ρ^n) :
    ‖T f‖≤ρ*‖f‖ := by
  by_cases h : f=0
  · simp [h]
  obtain ⟨C,hC⟩ := bound
  exact first_step_of_log_convex (fun n => ‖linearOrbit T f n‖) ρ C ρ0
    (norm_pos_iff.mpr h) (symmetric_orbit_log_convex T hs f) hC

#print axioms symmetric_first_step_from_power
end RobustFolkman.GeometricGap
