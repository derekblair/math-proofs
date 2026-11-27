import GeometricShiftedRate
import GeometricCapMass

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory

theorem capRate_residual (t : ℝ) :
    edgeRateClosed (t/(1+t))=capRate t := rfl

/-- The expected degree scale of the retained residual sphere is
polynomial, before the fixed positive shell fraction is applied. -/
theorem polynomial_residual_degree (t X : ℝ) (tp : 0<t) (ts : t≤1/40000)
    (Xp : 0<X) (gate : edgeRateClosed t+capRate t<X) :
    ∃ η B : ℝ, 0<η ∧ 1≤B ∧ ∀ N : ℝ, B≤N →
    ∀ (E W : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
      [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
      [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W],
    Module.finrank ℝ E=graphDimension X N → Module.finrank ℝ W+1=graphDimension X N →
    N^η ≤ N*(patternMass (E:=E) edgeCon t).toReal*
      (patternMass (E:=W) edgeCon (t/(1+t))).toReal := by
  let c := t/(1+t)
  have cp : 0<c := by dsimp [c]; positivity
  have cs : c≤1/40000 := by
    have p : c≤t := by
      apply (div_le_iff₀ (by positivity : 0<1+t)).2
      nlinarith only [sq_nonneg t]
    exact p.trans ts
  have ts' : t≤1/20000 := by linarith only [ts]
  have cs' : c≤1/20000 := by linarith only [cs]
  obtain ⟨A,a⟩ := gram_max_exists edgeCon edgeCon_sym (by decide) t tp ts'
  obtain ⟨D,d⟩ := gram_max_exists edgeCon edgeCon_sym (by decide) c cp cs'
  let slack := 1-(edgeRateClosed t+capRate t)/X
  have sp : 0<slack := by
    dsimp [slack]
    exact sub_pos.mpr ((div_lt_iff₀ Xp).2 (by simpa using gate))
  let δ := slack/4
  let η := slack/2
  have δp : 0<δ := by dsimp [δ]; positivity
  obtain ⟨B,b,Bprog⟩ := sphere_pattern_power_rates_shift 0 edgeCon edgeCon_sym
    (by decide) t tp ts A a.1 a.2 X δ Xp δp
  obtain ⟨C,c1,Cprog⟩ := sphere_pattern_power_rates_shift 1 edgeCon edgeCon_sym
    (by decide) c cp cs D d.1 d.2 X δ Xp δp
  refine ⟨η,max B C,by dsimp [η]; positivity,b.trans (le_max_left _ _),?_⟩
  intro N hN E W _ _ _ _ _ _ _ _ _ _ _ _ dimE dimW
  have hB := (le_max_left B C).trans hN
  have hC := (le_max_right B C).trans hN
  have Np : 0<N := zero_lt_one.trans_le (b.trans hB)
  have te := (Bprog N hB E (by simpa using dimE)).1
  have cq := (Cprog N hC W dimW).1
  have AR : Real.log A.det/(2*X)= -edgeRateClosed t/X := by
    unfold edgeRateClosed
    rw [edge_det_exact t tp ts' A a]
    ring
  have DR : Real.log D.det/(2*X)= -capRate t/X := by
    rw [←capRate_residual]
    change Real.log D.det/(2*X)= -edgeRateClosed c/X
    unfold edgeRateClosed
    rw [edge_det_exact c cp cs' D d]
    ring
  rw [AR] at te
  rw [DR] at cq
  have T : N^(-edgeRateClosed t/X-δ)≤(patternMass (E:=E) edgeCon t).toReal := te
  have Q : N^(-capRate t/X-δ)≤(patternMass (E:=W) edgeCon c).toReal := cq
  have s : η = 1+(-edgeRateClosed t/X-δ)+(-capRate t/X-δ) := by
    dsimp [η,δ,slack]
    ring
  rw [s,Real.rpow_add Np,Real.rpow_add Np,Real.rpow_one]
  exact mul_le_mul (mul_le_mul_of_nonneg_left T Np.le) Q (by positivity)
    (mul_nonneg Np.le ENNReal.toReal_nonneg)

#print axioms polynomial_residual_degree
end RobustFolkman.GeometricGap
