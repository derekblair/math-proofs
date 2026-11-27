import GeometricShellWeight

namespace RobustFolkman.GeometricGap

noncomputable def residualThreshold (t a b : ℝ) : ℝ :=
  (t-a*b)/Real.sqrt ((1-a^2)*(1-b^2))

/-- A two-sided bracket on the residual edge threshold, with no
derivatives: the upper bound uses the larger of the two heights. -/
theorem residual_threshold_thin_shell (t w a b : ℝ)
    (t0 : 0<t) (t1 : t≤1/8) (w0 : 0≤w) (w1 : w≤t)
    (ta : t≤a) (aw : a≤t+w) (bt : t≤b) (bw : b≤t+w) :
    t/(1+t)-4*t*w ≤ residualThreshold t a b ∧ residualThreshold t a b ≤ t/(1+t) := by
  let h := max a b
  have a0 : 0≤a := t0.le.trans ta
  have b0 : 0≤b := t0.le.trans bt
  have h0 : 0≤h := a0.trans (le_max_left _ _)
  have ht : t≤h := ta.trans (le_max_left _ _)
  have hw : h≤t+w := max_le aw bw
  have hs : h≤1/4 := by linarith only [hw,w1,t1]
  have ha := (le_max_left a b)
  have hb := (le_max_right a b)
  have hpos : 0<1-h^2 := by
    have hh := pow_le_pow_left₀ h0 hs 2
    linarith only [hh]
  have da : 1-h^2≤1-a^2 := by linarith only [pow_le_pow_left₀ a0 ha 2]
  have db : 1-h^2≤1-b^2 := by linarith only [pow_le_pow_left₀ b0 hb 2]
  let D := Real.sqrt ((1-a^2)*(1-b^2))
  have Dlo : 1-h^2≤D := by
    have m := mul_le_mul da db hpos.le (hpos.le.trans da)
    change 1-h^2 ≤ Real.sqrt ((1-a^2)*(1-b^2))
    conv_lhs => rw [← Real.sqrt_sq hpos.le]
    exact Real.sqrt_le_sqrt (by nlinarith only [m])
  have Dp : 0<D := hpos.trans_le Dlo
  have tp : 0<1-t^2 := by
    have tt := pow_le_pow_left₀ t0.le t1 2
    linarith only [tt]
  have Dhi : D≤1-t^2 := by
    have da' : 1-a^2≤1-t^2 := by linarith only [pow_le_pow_left₀ t0.le ta 2]
    have db' : 1-b^2≤1-t^2 := by linarith only [pow_le_pow_left₀ t0.le bt 2]
    have m := mul_le_mul da' db' (hpos.le.trans db) tp.le
    change Real.sqrt ((1-a^2)*(1-b^2)) ≤ 1-t^2
    conv_rhs => rw [← Real.sqrt_sq tp.le]
    exact Real.sqrt_le_sqrt (by nlinarith only [m])
  have aB : a≤2*t := by linarith only [aw,w1]
  have bB : b≤2*t := by linarith only [bw,w1]
  have N0 : 0≤t-a*b := by
    have hh := mul_le_mul aB bB b0 (by positivity : 0≤2*t)
    have tt := mul_le_mul_of_nonneg_left (show 4*t≤1 by linarith only [t1]) t0.le
    nlinarith only [hh,tt]
  have pHi : a*b≤(t+w)^2 := by
    have m := mul_le_mul aw bw b0 (by positivity : 0≤t+w)
    nlinarith only [m]
  have pLo : t*h≤a*b := by
    rcases le_total a b with e|e
    · rw [show h=b from max_eq_right e]
      exact mul_le_mul_of_nonneg_right ta b0
    · rw [show h=a from max_eq_left e]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left bt a0
  have E : (t-t^2)/(1-t^2)=t/(1+t) := by
    field_simp [tp.ne',show 1+t≠0 by positivity]
    ring
  constructor
  · change _ ≤ (t-a*b)/D
    apply le_trans ?_ (div_le_div_of_nonneg_left N0 Dp Dhi)
    apply (le_div_iff₀ tp).2
    rw [←E,sub_mul,div_mul_cancel₀ _ tp.ne']
    have ua := mul_le_mul_of_nonneg_right w1 w0
    have ub := mul_le_mul_of_nonneg_right (show 4*t^2≤1 by nlinarith only [pow_le_pow_left₀ t0.le t1 2])
      (show 0≤t*w by positivity)
    nlinarith only [pHi,ua,ub]
  · change (t-a*b)/D ≤ _
    apply (div_le_div_of_nonneg_left N0 hpos Dlo).trans
    apply ((div_le_div_iff₀ hpos (show 0<1+t by positivity)).2 ?_)
    have a := mul_le_mul_of_nonneg_right (show t-a*b≤t-t*h by linarith only [pLo])
      (show 0≤1+t by positivity)
    have b := mul_le_mul_of_nonneg_right ht (show 0≤t*(1-h) by
      have : 0≤1-h := by linarith only [hs]
      positivity)
    nlinarith only [a,b]
#print axioms residual_threshold_thin_shell
end RobustFolkman.GeometricGap
