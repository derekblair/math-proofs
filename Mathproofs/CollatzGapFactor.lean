import Mathproofs.CollatzGapC22C25

/-!
# The explicit gap factor and its logarithmic bridge

This module defines the actual product of the Q-ratio and the power-of-two
ratio appearing in the analytic model. It proves the logarithmic identities
and the conditional odd-block minimum for that factor, rather than for an
arbitrary objective with an assumed difference bridge.

Parameters follow `CollatzGapConvex`: qp=q′, qpp=q″, d=δ′, e=δ_n,
Q(t)=t·qp+qpp, x(t)=(a−t)·d+e. All parameters remain abstract here.
There is no assertion identifying them with Collatz dynamics or the
continued fraction of log₂(3).
-/

namespace CollatzGapFactor

/-- The explicit gap factor, with real exponentiation base two. -/
noncomputable def factor (qp qpp a d e t : ℝ) : ℝ :=
  (gapQ qp qpp (t+1) / gapQ qp qpp t) *
    (((2 : ℝ) ^ gapx a d e t - 1) / ((2 : ℝ) ^ gapx a d e (t+1) - 1))

private theorem q_pos {qp qpp t : ℝ} (hqp : 0 < qp) (hqpp : 0 < qpp)
    (ht : 0 ≤ t) : 0 < gapQ qp qpp t := by
  unfold gapQ
  positivity

private theorem power_sub_one_pos {a d e t : ℝ} (hd : 0 < d) (he : 0 < e)
    (hta : t ≤ a) : 0 < (2 : ℝ) ^ gapx a d e t - 1 := by
  have hx : 0 < gapx a d e t := by
    unfold gapx
    have : 0 ≤ a-t := sub_nonneg.mpr hta
    positivity
  exact sub_pos.mpr (Real.one_lt_rpow (by norm_num) hx)

/-- All factors and denominators are positive throughout the factor domain. -/
theorem factor_pos {qp qpp a d e t : ℝ}
    (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (he : 0 < e)
    (ht : 1 ≤ t) (hta : t+1 ≤ a) : 0 < factor qp qpp a d e t := by
  exact mul_pos (div_pos (q_pos hqp hqpp (by linarith)) (q_pos hqp hqpp (by linarith)))
    (div_pos (power_sub_one_pos hd he (by linarith)) (power_sub_one_pos hd he hta))

/-- The logarithm of the explicit product is exactly its T-plus-S form. -/
theorem log_factor {qp qpp a d e t : ℝ}
    (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (he : 0 < e)
    (ht : 1 ≤ t) (hta : t+1 ≤ a) :
    Real.log (factor qp qpp a d e t) = gapT qp qpp t + gapS d (gapx a d e t) := by
  have hQ0 := q_pos hqp hqpp (show 0 ≤ t by linarith)
  have hQ1 := q_pos hqp hqpp (show 0 ≤ t+1 by linarith)
  have hP0 := power_sub_one_pos hd he (show t ≤ a by linarith)
  have hP1 := power_sub_one_pos hd he hta
  have hQ : gapQ qp qpp (t+1) / gapQ qp qpp t = 1 + qp/(t*qp+qpp) := by
    have hne : t*qp+qpp ≠ 0 := ne_of_gt hQ0
    unfold gapQ
    field_simp
    ring
  have hx : gapx a d e (t+1) = gapx a d e t - d := by unfold gapx; ring
  unfold factor
  rw [Real.log_mul (ne_of_gt (div_pos hQ1 hQ0)) (ne_of_gt (div_pos hP0 hP1)), hQ, hx]
  rfl

/-- The explicit factor's logarithmic first difference is the existing
analytic criterion, wherever both neighboring factors are in the domain. -/
theorem log_factor_diff {qp qpp a d e t : ℝ}
    (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (he : 0 < e)
    (ht : 1 ≤ t) (hta : t+2 ≤ a) :
    Real.log (factor qp qpp a d e (t+1)) - Real.log (factor qp qpp a d e t) =
      GapCF.gapDeltaLogT qp qpp d e a t := by
  rw [log_factor hqp hqpp hd he (by linarith : 1 ≤ t+1) (by linarith : t+1+1 ≤ a),
    log_factor hqp hqpp hd he ht (by linarith : t+1 ≤ a)]
  rw [← GapCF.gapDelta_eq_gapDeltaLogT hqp hqpp hd he ht hta]
  unfold gapDelta gapu gapx
  ring

/-- Natural-index bridge on the full interior of an odd block. -/
theorem odd_log_factor_diff {qp qpp d e : ℝ} {m t : ℕ}
    (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (he : 0 < e)
    (ht : 1 ≤ t) (htm : t ≤ 2*m-1) :
    Real.log (factor qp qpp (2*(m:ℝ)+1) d e ((t+1:ℕ):ℝ)) -
      Real.log (factor qp qpp (2*(m:ℝ)+1) d e (t:ℝ)) =
      GapCF.gapDeltaLogT qp qpp d e (2*(m:ℝ)+1) (t:ℝ) := by
  have hm : 1 ≤ m := by omega
  have hbound : t+1 ≤ 2*m := by omega
  have hboundR : (t:ℝ)+1 ≤ 2*(m:ℝ) := by exact_mod_cast hbound
  simpa only [Nat.cast_add, Nat.cast_one] using
    log_factor_diff hqp hqpp hd he (by exact_mod_cast ht) (by linarith)

/-- Positivity throughout the natural-index odd block. -/
theorem odd_factor_pos {qp qpp d e : ℝ} {m t : ℕ}
    (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (he : 0 < e)
    (ht : 1 ≤ t) (htm : t ≤ 2*m) :
    0 < factor qp qpp (2*(m:ℝ)+1) d e (t:ℝ) := by
  have hbound : (t:ℝ) ≤ 2*(m:ℝ) := by exact_mod_cast htm
  exact factor_pos hqp hqpp hd he (by exact_mod_cast ht) (by linarith)

/-- A minimizer of the explicit factor is m under the existing C22 hypotheses.
The logarithmic bridge is proved above and is not a theorem argument. -/
theorem c22_factor_argmin {tstar m : ℕ} {qp qpp d e rho r : ℝ}
    (hm : 2 ≤ m) (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (he : 0 < e)
    (hqpp_le : qpp ≤ qp) (hr : 0 ≤ r) (hrho : 0 < rho) (hrho1 : rho < 1)
    (he_eq : e = rho*d) (hqpp_eq : qpp = r*qp)
    (hd_eq : d = 1/(qp*(2*(m:ℝ)+1+r+rho)))
    (hL : (Real.log 2)^2 ≤ 192*qpp*qp^2/((2*(m:ℝ)+2)*qp+qpp))
    (hdom : 1 ≤ tstar ∧ tstar ≤ 2*m)
    (harg : ∀ t : ℕ, 1 ≤ t → t ≤ 2*m →
      factor qp qpp (2*(m:ℝ)+1) d e tstar ≤ factor qp qpp (2*(m:ℝ)+1) d e t) :
    tstar = m := by
  apply GapCF.c22_argmin (g := fun t : ℕ => Real.log (factor qp qpp (2*(m:ℝ)+1) d e t))
    hm hqp hqpp hd he hqpp_le hr hrho hrho1 he_eq hqpp_eq hd_eq hL hdom
  · intro t ht htM
    apply (Real.log_le_log_iff
      (odd_factor_pos hqp hqpp hd he hdom.1 hdom.2)
      (odd_factor_pos hqp hqpp hd he ht htM)).mpr
    exact harg t ht htM
  · exact fun t ht htM => odd_log_factor_diff hqp hqpp hd he ht htM

/-- The actual factor has its unique minimum at m on {1,…,2m}, under
C22's quantitative hypotheses. Existence is supplied by finite minimization;
neither an argmin nor a logarithmic bridge is assumed. -/
theorem c22_factor_unique_min {m : ℕ} {qp qpp d e rho r : ℝ}
    (hm : 2 ≤ m) (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (he : 0 < e)
    (hqpp_le : qpp ≤ qp) (hr : 0 ≤ r) (hrho : 0 < rho) (hrho1 : rho < 1)
    (he_eq : e = rho*d) (hqpp_eq : qpp = r*qp)
    (hd_eq : d = 1/(qp*(2*(m:ℝ)+1+r+rho)))
    (hL : (Real.log 2)^2 ≤ 192*qpp*qp^2/((2*(m:ℝ)+2)*qp+qpp)) :
    (1 ≤ m ∧ m ≤ 2*m) ∧
      ∀ t : ℕ, 1 ≤ t → t ≤ 2*m → t ≠ m →
        factor qp qpp (2*(m:ℝ)+1) d e m < factor qp qpp (2*(m:ℝ)+1) d e t := by
  classical
  let f : ℕ → ℝ := fun t => factor qp qpp (2*(m:ℝ)+1) d e t
  have hnon : (Finset.Icc 1 (2*m)).Nonempty := ⟨m, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  obtain ⟨s, hs, hsmin⟩ := (Finset.Icc 1 (2*m)).exists_min_image f hnon
  have hmin : ∀ t : ℕ, 1 ≤ t → t ≤ 2*m → f s ≤ f t :=
    fun t ht htM => hsmin t (Finset.mem_Icc.mpr ⟨ht, htM⟩)
  have hsm : s = m := c22_factor_argmin hm hqp hqpp hd he hqpp_le hr hrho hrho1
    he_eq hqpp_eq hd_eq hL (Finset.mem_Icc.mp hs) hmin
  have hmmin : ∀ t : ℕ, 1 ≤ t → t ≤ 2*m → f m ≤ f t := by
    simpa only [hsm] using hmin
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro t ht htM htm
  change f m < f t
  by_contra hnot
  have htmin : ∀ j : ℕ, 1 ≤ j → j ≤ 2*m → f t ≤ f j :=
    fun j hj hjM => le_trans (le_of_not_gt hnot) (hmmin j hj hjM)
  exact htm (c22_factor_argmin hm hqp hqpp hd he hqpp_le hr hrho hrho1
    he_eq hqpp_eq hd_eq hL ⟨ht, htM⟩ htmin)

end CollatzGapFactor
