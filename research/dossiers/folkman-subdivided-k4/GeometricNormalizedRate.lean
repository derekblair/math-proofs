import GeometricLogBounds

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory
open scoped ENNReal
variable {I : Type*} [Fintype I] [LinearOrder I]

noncomputable def patternIntegral (C : I→I→Prop) (t p : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in chartRegion C t, (ENNReal.ofReal (gramChart x).det)^p

/-- This proves the exact exponential rate of the normalized determinant
integral, without assuming it is already the law of spherical Gram data. -/
theorem normalized_determinant_log_rate (C : I→I→Prop)
    (sym : ∀ i j, C i j ↔ C j i) (n : Fintype.card I≤6)
    (t : ℝ) (t0 : 0<t) (ts : t≤1/40000) (M : Matrix I I ℝ)
    (mf : GramFeasible C t M) (max : ∀ A, GramFeasible C t A → A.det≤M.det)
    (ε : ℝ) (e0 : 0<ε) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ p : ℝ, cutoff ≤ p →
      0 < patternIntegral C t p ∧ patternIntegral C t p < ∞ ∧
      0 < patternIntegral (fun _ _ : I => False) (1/40000) p ∧
      patternIntegral (fun _ _ : I => False) (1/40000) p < ∞ ∧
      |(Real.log (patternIntegral C t p).toReal -
        Real.log (patternIntegral (fun _ _ : I => False) (1/40000) p).toReal)/p -
        Real.log M.det| ≤ ε := by
  classical
  let θ := ε/4
  have th : 0<θ := by dsimp [θ]; positivity
  have mp : 0<M.det :=
    (optimum_is_localized C sym n t t0 (by linarith only [ts]) M mf max).1.det_pos
  let b := Real.exp (Real.log M.det-θ)
  let a := Real.exp (-θ)
  have bp : 0<b := Real.exp_pos _
  have ap : 0<a := Real.exp_pos _
  have bl : b<M.det := by
    have h := Real.exp_lt_exp.mpr (sub_lt_self (Real.log M.det) th)
    rwa [Real.exp_log mp] at h
  have al : a<1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos th)
  obtain ⟨c,cp,ct,cb⟩ := chart_determinant_sandwich C sym n t t0 ts M mf max b bl
  obtain ⟨u,up,ut,ub⟩ := chart_normalizer_sandwich (I:=I) n a al
  let V := volume (chartRegion C t)
  let W := volume (chartRegion (fun _ _ : I => False) (1/40000))
  let A := Real.log c.toReal-Real.log W.toReal
  let B := Real.log V.toReal-Real.log u.toReal
  let K := (|A|+|B|)/θ + 1
  have kp : 0<K := by dsimp [K]; positivity
  refine ⟨K,kp,?_⟩
  intro p hp
  have pp : 0<p := kp.trans_le hp
  have cbp := cb p pp.le
  have ubp := ub p pp.le
  let F := patternIntegral C t p
  let D := patternIntegral (fun _ _ : I => False) (1/40000) p
  have Dt : D ≤ (ENNReal.ofReal 1)^p*W := by simpa [D, W, patternIntegral] using ubp.2
  obtain ⟨fp,ft,_,fl,fh⟩ := log_of_power_sandwich b M.det p bp mp pp.le c V F cp ct
    (chartRegion_volume_lt_top C t) cbp.1 cbp.2
  obtain ⟨dp,dt,_,dl,dh⟩ := log_of_power_sandwich a 1 p ap one_pos pp.le u W D up ut
    (chartRegion_volume_lt_top _ _) ubp.1 Dt
  have mid := mul_le_mul_of_nonneg_right hp th.le
  have ke : K*θ = |A|+|B|+θ := by dsimp [K]; field_simp
  rw [ke] at mid
  have largeA : -p*θ ≤ A := by
    have q := neg_abs_le A
    linarith only [mid,q,abs_nonneg B,th]
  have largeB : B ≤ p*θ := by
    have q := le_abs_self B
    linarith only [mid,q,abs_nonneg A,th]
  rw [show Real.log b = Real.log M.det-θ from Real.log_exp _] at fl
  rw [show Real.log a = -θ from Real.log_exp _] at dl
  simp only [Real.log_one,mul_zero,zero_add] at dh
  refine ⟨fp,ft,dp,dt,?_⟩
  change |(Real.log F.toReal-Real.log D.toReal)/p-Real.log M.det|≤ε
  apply abs_le.mpr
  constructor
  · have h : (Real.log M.det-ε)*p ≤ Real.log F.toReal-Real.log D.toReal := by
      dsimp [A] at largeA
      have δ : p*θ≥0 := by positivity
      have θid : ε=4*θ := by dsimp [θ]; ring
      rw [θid]
      nlinarith only [fl,dh,largeA,δ]
    have h' := (le_div_iff₀ pp).mpr h
    linarith only [h']
  · have h : Real.log F.toReal-Real.log D.toReal ≤ (Real.log M.det+ε)*p := by
      dsimp [B] at largeB
      have δ : p*θ≥0 := by positivity
      have θid : ε=4*θ := by dsimp [θ]; ring
      rw [θid]
      nlinarith only [fh,dl,largeB,δ]
    have h' := (div_le_iff₀ pp).mpr h
    linarith only [h']

#print axioms normalized_determinant_log_rate
end RobustFolkman.GeometricGap
