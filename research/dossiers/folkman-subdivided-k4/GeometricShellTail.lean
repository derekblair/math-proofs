import GeometricShellIntegral

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped ENNReal

def excessCube (w : ℝ) : Set ThreeReals :=
  Icc 0 w ×ˢ (Icc 0 w ×ˢ Icc 0 w)

noncomputable def shellWeight (t m : ℝ) (p : ThreeReals) : ℝ≥0∞ :=
  ENNReal.ofReal ((threeGramDet (t+p.1) (t+p.2.1) (t+p.2.2) /
      threeGramDet t t t)^m)

theorem volume_excessCube {w : ℝ} (w0 : 0≤w) :
    (volume : Measure ThreeReals) (excessCube w) = ENNReal.ofReal (w^3) := by
  change ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume))
    (Icc 0 w ×ˢ (Icc 0 w ×ˢ Icc 0 w)) = _
  rw [Measure.prod_prod,Measure.prod_prod,Real.volume_Icc,sub_zero]
  rw [←ENNReal.ofReal_mul w0,←ENNReal.ofReal_mul w0]
  congr 1
  ring

theorem shell_lower_integral (t m : ℝ) (t0 : 0<t) (t1 : t≤1/4) (m36 : 36≤m)
    (dense : 1≤m*t^2) (G : Set ThreeReals)
    (inside : excessCube (1/(m*t)) ⊆ G) :
    ENNReal.ofReal (Real.exp (-36)/(m*t)^3) ≤ ∫⁻ p in G, shellWeight t m p := by
  have k0 : 0<m*t := mul_pos (by linarith) t0
  refine le_trans ?_ (lintegral_mono_set inside)
  have H : (∫⁻ _ : ThreeReals in excessCube (1/(m*t)), ENNReal.ofReal (Real.exp (-36))) ≤
      ∫⁻ p in excessCube (1/(m*t)), shellWeight t m p := by
    apply setLIntegral_mono'
    · exact measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)
    · intro p hp
      exact ENNReal.ofReal_le_ofReal
        (triangle_shell_lower_weight t p.1 p.2.1 p.2.2 m t0 t1 m36 dense
          hp.1.1 hp.2.1.1 hp.2.2.1 hp.1.2 hp.2.1.2 hp.2.2.2)
  rw [lintegral_const, Measure.restrict_apply_univ, volume_excessCube (by positivity),
    ←ENNReal.ofReal_mul (Real.exp_pos _).le] at H
  convert H using 1
  congr 1
  ring

/-- In the valid excess chart, moving any nonnegative coordinate
threshold farther out has an exponential penalty. -/
theorem shell_orthant_mass_bound (t m a b c : ℝ) (t0 : 0<t) (t1 : t≤1/4) (m36 : 36≤m)
    (dense : 1≤m*t^2) (G : Set ThreeReals)
    (inside : excessCube (1/(m*t)) ⊆ G) (within : G ⊆ excessCube (1-t))
    (pd : ∀ p∈G, 0≤threeGramDet (t+p.1) (t+p.2.1) (t+p.2.2)) :
    (∫⁻ p in G ∩ (Ici a ×ˢ (Ici b ×ˢ Ici c)), shellWeight t m p) ≤
      ENNReal.ofReal (Real.exp (36-m*t*(a+b+c))) * (∫⁻ p in G, shellWeight t m p) := by
  have m0 : 0<m := by linarith
  have k0 : 0<m*t := mul_pos m0 t0
  have meas : Measurable (shiftedExponential (m*t)) := by unfold shiftedExponential; fun_prop
  calc
    _ ≤ ∫⁻ p in G ∩ (Ici a ×ˢ (Ici b ×ˢ Ici c)), shiftedExponential (m*t) p := by
      apply setLIntegral_mono meas
      intro p hp
      have cc := within hp.1
      apply ENNReal.ofReal_le_ofReal
      simp only [neg_mul] at *
      simpa only [neg_mul] using triangle_shell_upper_weight t p.1 p.2.1 p.2.2 m t0.le t1 m0
        cc.1.1 cc.2.1.1 cc.2.2.1 cc.1.2 cc.2.1.2 cc.2.2.2 (pd p hp.1)
    _ ≤ ∫⁻ p in Ici a ×ˢ (Ici b ×ˢ Ici c), shiftedExponential (m*t) p :=
      lintegral_mono_set inter_subset_right
    _ = ENNReal.ofReal (Real.exp (36-m*t*(a+b+c))) *
        ENNReal.ofReal (Real.exp (-36)/(m*t)^3) := by
      rw [orthant_exp_integral (m*t) a b c k0,←ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      rw [←mul_div_assoc,←Real.exp_add]
      congr 2
      ring
    _ ≤ _ := by
      gcongr
      exact shell_lower_integral t m t0 t1 m36 dense G inside

#print axioms shell_orthant_mass_bound
end RobustFolkman.GeometricGap
