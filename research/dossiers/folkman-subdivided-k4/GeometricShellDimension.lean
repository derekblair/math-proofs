import GeometricShellScales

namespace RobustFolkman.GeometricGap

theorem eventual_shell_dimension (t X : ℝ) (tp : 0<t) (ts : t≤1/40000) (Xp : 0<X) :
    ∃ H : ℝ, Real.exp 1≤H ∧ ∀ N≥H,
      let n := graphDimension X N-4
      let m := n+1
      let c := t/(1+t)
      graphDimension X N=n+4 ∧
      (n:ℝ)≤(1/X+1)*Real.log N ∧
      36≤(n:ℝ)/2 ∧ 100≤((m:ℝ)/2)*t^2 ∧
      3≤(n:ℝ)/2 ∧ 1≤4*((n:ℝ)/2)*c^2 ∧
      Real.sqrt (squaredCapContraction n c)≤1/200 := by
  let c := t/(1+t)
  have cp : 0<c := by dsimp [c]; positivity
  have c1 : c≤1/40000 := by
    have z : c≤t := (div_le_iff₀ (by positivity : 0<1+t)).2 (by nlinarith only [sq_nonneg t])
    exact z.trans ts
  obtain ⟨n₀,g⟩ := cap_gap_small_eventually c cp c1
  let K := max (max ((n₀:ℝ)+4) 80) (200/t^2+4)
  let H := max (Real.exp 1) (Real.exp (X*K))
  refine ⟨H,le_max_left _ _,?_⟩
  intro N NH n m c'
  have Kb : Real.exp (X*K)≤N := (le_max_right _ _).trans NH
  have e1 : Real.exp 1≤N := (le_max_left _ _).trans NH
  have Np : 0<N := (Real.exp_pos _).trans_le e1
  have log1 : 1≤Real.log N := by
    have p := Real.log_le_log (Real.exp_pos 1) e1
    rwa [Real.log_exp] at p
  have log : K≤Real.log N/X := by
    have h := Real.log_le_log (Real.exp_pos _) Kb
    rw [Real.log_exp] at h
    exact (le_div_iff₀ Xp).2 (by linarith only [h])
  have dl := log.trans (Nat.le_ceil (Real.log N/X))
  change K≤(graphDimension X N:ℝ) at dl
  have maxl : max ((n₀:ℝ)+4) 80≤(graphDimension X N:ℝ) :=
    (le_max_left _ _).trans dl
  have N0 : n₀+4≤graphDimension X N := by
    exact_mod_cast (le_max_left ((n₀:ℝ)+4) (80:ℝ)).trans maxl
  have d0 : graphDimension X N=n+4 := by dsimp [n]; omega
  have dd : (graphDimension X N:ℝ)=(n:ℝ)+4 := by exact_mod_cast d0
  have n0 : n₀≤n := by omega
  have bd : (n:ℝ)≤(1/X+1)*Real.log N := by
    have du := Nat.ceil_lt_add_one (div_nonneg (by linarith only [log1] : 0≤Real.log N) Xp.le)
    change (graphDimension X N:ℝ)<Real.log N/X+1 at du
    rw [dd] at du
    rw [show (1/X+1)*Real.log N=Real.log N/X+Real.log N by ring]
    linarith only [du,log1]
  have mL : 36≤(n:ℝ)/2 := by
    have h := (le_max_right ((n₀:ℝ)+4) (80:ℝ)).trans maxl
    rw [dd] at h
    linarith only [h]
  have h := (le_max_right (max ((n₀:ℝ)+4) 80) (200/t^2+4)).trans dl
  rw [dd] at h
  have r : 200≤(n:ℝ)*t^2 := (div_le_iff₀ (sq_pos_of_pos tp)).1 (by linarith only [h])
  have rr : 100≤((m:ℝ)/2)*t^2 := by
    dsimp [m]
    push_cast
    nlinarith only [r,sq_nonneg t]
  exact ⟨d0,bd,mL,rr,g n n0⟩

#print axioms eventual_shell_dimension
end RobustFolkman.GeometricGap
