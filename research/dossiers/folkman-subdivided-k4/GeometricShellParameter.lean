import GeometricSphericalCompare
import GeometricResidualDegree

namespace RobustFolkman.GeometricGap

/-- One fixed threshold makes the gap between the two residual graphs
arbitrarily small; no choice depending on the sample size is needed. -/
theorem choose_small_shell_threshold (A ε : ℝ) (Ap : 0<A) (ep : 0<ε) :
    ∃ t : ℝ, 0<t ∧ t≤1/40000 ∧
      ∀ r : ℝ, 0<r → let c := t/(1+t); let w := A/(r*t);
      let s := 4*t*w; (4*r*c*s)*Real.exp (3+4*r*c*s) ≤ ε := by
  let K := 16*A
  have Kp : 0<K := by dsimp [K]; positivity
  let t : ℝ := min (1/80000) (min (1/K) (ε/(K*Real.exp 4)))
  have tp : 0<t := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have t1 : t≤1/80000 := min_le_left _ _
  have tx : t≤1/K := (min_le_right _ _).trans (min_le_left _ _)
  have te : t≤ε/(K*Real.exp 4) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨t,tp,t1.trans (by norm_num),?_⟩
  intro r rp c w s
  have ct : c≤t := (div_le_iff₀ (by positivity : 0<1+t)).2 (by nlinarith only [sq_nonneg t])
  have cp : 0<c := by dsimp [c]; positivity
  have eq : 4*r*c*s=K*c := by
    dsimp [s,w,K]
    field_simp [rp.ne',tp.ne']
    ring
  have h1 : K*c≤1 := by
    have h := (le_div_iff₀ Kp).1 (ct.trans tx)
    simpa only [mul_comm] using h
  have hε : (K*c)*Real.exp 4 ≤ ε := by
    have h := (le_div_iff₀ (mul_pos Kp (Real.exp_pos _))).1 (ct.trans te)
    linarith only [show c*(K*Real.exp 4)=(K*c)*Real.exp 4 by ring,h]
  rw [eq]
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [h1]))
    (mul_nonneg Kp.le cp.le)).trans hε

#print axioms choose_small_shell_threshold
end RobustFolkman.GeometricGap
