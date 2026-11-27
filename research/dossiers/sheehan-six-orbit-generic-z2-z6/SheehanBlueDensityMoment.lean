import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

open scoped BigOperators

namespace SheehanBlueDensity

/-- Constant Fourier coefficient of the unnormalized squared triangular array. -/
def diagonal (K : ℕ) : ℚ :=
  (K : ℚ)^2 + 2 * ∑ j ∈ Finset.range K, (j : ℚ)^2

/-- First neighbor Fourier coefficient of the unnormalized squared triangular array. -/
def neighbor (K : ℕ) : ℚ :=
  2 * ∑ j ∈ Finset.range K, (j : ℚ) * ((j : ℚ) + 1)

theorem diagonal_formula (K : ℕ) :
    diagonal K = (K : ℚ) * (2 * (K : ℚ)^2 + 1) / 3 := by
  induction K with
  | zero => norm_num [diagonal]
  | succ n ih =>
    unfold diagonal at ih ⊢
    rw [Finset.sum_range_succ, Nat.cast_succ]
    linarith only [ih, show
      ((n : ℚ) + 1) * (2 * ((n : ℚ) + 1)^2 + 1) / 3 -
      (n : ℚ) * (2 * (n : ℚ)^2 + 1) / 3 =
      ((n : ℚ) + 1)^2 - (n : ℚ)^2 + 2 * (n : ℚ)^2 by ring]

theorem diagonal_sub_neighbor (K : ℕ) :
    diagonal K - neighbor K = (K : ℚ) := by
  induction K with
  | zero => norm_num [diagonal, neighbor]
  | succ n ih =>
    unfold diagonal neighbor at ih ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Nat.cast_succ]
    linarith only [ih, show
      ((n : ℚ) + 1)^2 - (n : ℚ)^2 + 2 * (n : ℚ)^2 -
      2 * (n : ℚ) * ((n : ℚ) + 1) = 1 by ring]

/-- The moment of the squared normalized Fejér kernel, at the level of its
    exact diagonal and adjacent Fourier coefficient sums. -/
theorem normalized_moment (K : ℕ) (hK : K ≠ 0) :
    (diagonal K - neighbor K) / (2 * diagonal K) =
      3 / (2 * (2 * (K : ℚ)^2 + 1)) := by
  rw [diagonal_sub_neighbor, diagonal_formula]
  have h : (K : ℚ) ≠ 0 := by exact_mod_cast hK
  have hp : (2 * (K : ℚ)^2 + 1) ≠ 0 := by positivity
  field_simp

#print axioms normalized_moment


/-- The strict positivity margin in the degree-controlled box witness. -/
theorem positive_margin (ε K t : ℝ) (hscale : 1 ≤ K * ε)
    (ht : 4 * ε^2 ≤ t) :
    0 < t - 6 / (2*K^2+1) := by
  have hsq : 1 ≤ (K * ε)^2 := by
    nlinarith only [hscale, sq_nonneg (K * ε - 1)]
  have hden : 0 < 2*K^2+1 := by positivity
  apply sub_pos.mpr
  apply lt_of_lt_of_le _ ht
  apply (div_lt_iff₀ hden).mpr
  nlinarith only [hsq, sq_nonneg ε]

/-- If a nonnegative-weight cutoff has positive total, some sample lies
    strictly inside every coordinate threshold. -/
theorem exists_inside_of_positive_weighted_cutoff {ι κ : Type*} [Fintype κ]
    (s : Finset ι) (u : ι → κ → ℝ) (w : ι → ℝ) (t : ℝ)
    (hu : ∀ i j, 0 ≤ u i j) (hw : ∀ i, 0 ≤ w i)
    (h : 0 < ∑ i ∈ s, (t - ∑ j, u i j) * w i) :
    ∃ i ∈ s, ∀ j, u i j < t := by
  classical
  by_contra hn
  push Not at hn
  have hnonpos : ∑ i ∈ s, (t - ∑ j, u i j) * w i ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    obtain ⟨j, hj⟩ := hn i hi
    have htot : t ≤ ∑ k, u i k := by
      exact hj.trans (Finset.single_le_sum (fun k _ => hu i k) (Finset.mem_univ j))
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htot) (hw i)
  exact (not_lt_of_ge hnonpos) h

#print axioms positive_margin
#print axioms exists_inside_of_positive_weighted_cutoff


/-- The sine cutoff has at least the margin needed for a box of radius ε. -/
theorem sine_positive_margin (ε K : ℝ) (hε : 0 ≤ ε) (hε₂ : ε ≤ 1/2)
    (hscale : 1 ≤ K * ε) :
    0 < (Real.sin (Real.pi * ε))^2 - 6 / (2*K^2+1) := by
  apply positive_margin ε K _ hscale
  have h := Real.le_sin_mul (x := 2*ε) (by linarith) (by linarith)
  rw [show Real.pi / 2 * (2*ε) = Real.pi * ε by ring] at h
  nlinarith only [h, hε, mul_nonneg (show 0 ≤ Real.sin (Real.pi*ε) - 2*ε by linarith)
    (show 0 ≤ Real.sin (Real.pi*ε) + 2*ε by linarith)]

/-- In a cyclic sample, finite frequency sums with no nonconstant alias
    contribute exactly the zero-mode coefficient. -/
theorem cyclic_sample_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (z : ι) (hz : z ∈ s) (phase coef : ι → ℂ) (p : ℕ)
    (hzphase : phase z = 1)
    (hroot : ∀ i ∈ s, (phase i)^p = 1)
    (hnon : ∀ i ∈ s, i ≠ z → phase i ≠ 1) :
    (∑ h ∈ Finset.range p, ∑ i ∈ s, coef i * (phase i)^h) = p * coef z := by
  rw [Finset.sum_comm]
  calc
    (∑ i ∈ s, ∑ h ∈ Finset.range p, coef i * (phase i)^h) =
        ∑ i ∈ s, coef i * ∑ h ∈ Finset.range p, (phase i)^h := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = coef z * ∑ h ∈ Finset.range p, (phase z)^h := by
      apply Finset.sum_eq_single_of_mem z hz
      intro i hi hin
      rw [geom_sum_eq (hnon i hi hin), hroot i hi]
      simp
    _ = p * coef z := by simp [hzphase, mul_comm]

#print axioms sine_positive_margin
#print axioms cyclic_sample_sum


/-- One normalized kernel contributes less than 3/16 to an anisotropic cutoff. -/
theorem anisotropic_ratio_le (ε K : ℝ) (hε : 0 < ε) (hε₂ : ε ≤ 1/2)
    (hscale : 1 ≤ K * ε) :
    (3 / (2 * (2*K^2+1))) / (Real.sin (Real.pi * ε))^2 ≤ 3/16 := by
  have hs := Real.le_sin_mul (x := 2*ε) (by linarith) (by linarith)
  rw [show Real.pi / 2 * (2*ε) = Real.pi * ε by ring] at hs
  have ht : 4*ε^2 ≤ (Real.sin (Real.pi*ε))^2 := by
    nlinarith only [mul_nonneg (show 0 ≤ Real.sin (Real.pi*ε) - 2*ε by linarith)
      (show 0 ≤ Real.sin (Real.pi*ε) + 2*ε by linarith)]
  have hsin : 0 < (Real.sin (Real.pi * ε))^2 := by
    exact lt_of_lt_of_le (by positivity) ht
  have hden : 0 < 2 * (2*K^2+1) := by positivity
  have hsq : 1 ≤ (K * ε)^2 := by
    nlinarith only [hscale, sq_nonneg (K * ε - 1)]
  apply (div_le_iff₀ hsin).mpr
  apply (div_le_iff₀ hden).mpr
  have hm := mul_le_mul_of_nonneg_right ht hden.le
  nlinarith only [hsq, sq_nonneg ε, hm]

theorem anisotropic_four_positive (r : Fin 4 → ℝ) (hr : ∀ i, r i ≤ 3/16) :
    0 < 1 - ∑ i, r i := by
  have h : ∑ i, r i ≤ ∑ _i : Fin 4, (3/16 : ℝ) :=
    Finset.sum_le_sum (fun i _ => hr i)
  norm_num at h
  linarith

#print axioms anisotropic_ratio_le
#print axioms anisotropic_four_positive

end SheehanBlueDensity
