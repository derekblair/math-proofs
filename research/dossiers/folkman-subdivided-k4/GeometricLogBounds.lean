import GeometricNormalization

namespace RobustFolkman.GeometricGap
open scoped ENNReal

/-- Taking real logarithms does not silently drop zero or infinite masses. -/
theorem log_of_power_sandwich (b B p : ℝ) (b0 : 0 < b) (B0 : 0 < B)
    (p0 : 0 ≤ p) (c C z : ℝ≥0∞) (c0 : 0 < c) (ct : c < ∞) (Ct : C < ∞)
    (loh : (ENNReal.ofReal b)^p*c ≤ z)
    (hih : z ≤ (ENNReal.ofReal B)^p*C) :
    0 < z ∧ z < ∞ ∧ 0 < C ∧
    p*Real.log b+Real.log c.toReal ≤ Real.log z.toReal ∧
    Real.log z.toReal ≤ p*Real.log B+Real.log C.toReal := by
  have eb : 0 < ENNReal.ofReal b := ENNReal.ofReal_pos.mpr b0
  have eB : 0 < ENNReal.ofReal B := ENNReal.ofReal_pos.mpr B0
  have lp : 0 < (ENNReal.ofReal b)^p*c :=
    ENNReal.mul_pos (ENNReal.rpow_pos_of_nonneg eb p0).ne' c0.ne'
  have zp : 0 < z := lp.trans_le loh
  have Cp : 0 < C := by
    by_contra! h
    have cz : C = 0 := le_antisymm h bot_le
    simp [cz] at hih
    exact zp.ne' hih
  have ht : (ENNReal.ofReal B)^p*C ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg p0 ENNReal.ofReal_ne_top) Ct.ne
  have zt : z < ∞ := hih.trans_lt ht.lt_top
  have cr := ENNReal.toReal_pos c0.ne' ct.ne
  have Cr := ENNReal.toReal_pos Cp.ne' Ct.ne
  have zr := ENNReal.toReal_pos zp.ne' zt.ne
  have low := ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg p0 ENNReal.ofReal_ne_top) ct.ne) zt.ne |>.mpr loh
  have high := (ENNReal.toReal_le_toReal zt.ne ht).mpr hih
  rw [ENNReal.toReal_mul,← ENNReal.toReal_rpow,ENNReal.toReal_ofReal b0.le] at low
  rw [ENNReal.toReal_mul,← ENNReal.toReal_rpow,ENNReal.toReal_ofReal B0.le] at high
  have bp : 0 < b^p := Real.rpow_pos_of_pos b0 _
  have Bp : 0 < B^p := Real.rpow_pos_of_pos B0 _
  have hl := (Real.log_le_log_iff (mul_pos bp cr) zr).mpr low
  have hh := (Real.log_le_log_iff zr (mul_pos Bp Cr)).mpr high
  rw [Real.log_mul bp.ne' cr.ne',Real.log_rpow b0] at hl
  rw [Real.log_mul Bp.ne' Cr.ne',Real.log_rpow B0] at hh
  exact ⟨zp,zt,Cp,by linarith only [hl],by linarith only [hh]⟩

#print axioms log_of_power_sandwich
end RobustFolkman.GeometricGap
