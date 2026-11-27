import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory Set
open scoped ENNReal

namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X]

/-- A bounded symmetric real kernel. Pointwise symmetry avoids arbitrary
versions of a product-a.e. symmetric representative. -/
structure Kernel (X : Type*) [MeasurableSpace X] where
  W : X × X → ℝ
  measurable_W : Measurable W
  nonneg : ∀ z, 0 ≤ W z
  le_one : ∀ z, W z ≤ 1
  symm : ∀ x y, W (x,y)=W (y,x)

variable (μ : Measure X) [IsFiniteMeasure μ]

noncomputable def mass : ℝ := μ.real univ
noncomputable def deg (K : Kernel X) (x : X) : ℝ := ∫ y, K.W (x,y) ∂μ
noncomputable def density (K : Kernel X) : ℝ := ∫ x, deg μ K x ∂μ

lemma integrable_bounded {f : X → ℝ} (hf : Measurable f) {C : ℝ}
    (h₁ : ∀ x, 0≤f x) (h₂ : ∀ x, f x≤C) : Integrable f μ := by
  apply Integrable.of_bound hf.aestronglyMeasurable C
  exact ae_of_all _ (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (h₁ x)]; exact h₂ x)

lemma rowMeasurable (K : Kernel X) (x : X) : Measurable (fun y => K.W (x,y)) := by
  exact K.measurable_W.comp (measurable_const.prodMk measurable_id)

lemma row_integrable (K : Kernel X) (x : X) :
    Integrable (fun y => K.W (x,y)) μ :=
  integrable_bounded μ (rowMeasurable K x) (fun y => K.nonneg (x,y)) (fun y => K.le_one (x,y))

omit [IsFiniteMeasure μ] in
lemma deg_nonneg (K : Kernel X) (x : X) : 0≤deg μ K x := by
  unfold deg; exact integral_nonneg (fun y => K.nonneg (x,y))

lemma deg_le_mass (K : Kernel X) (x : X) : deg μ K x≤mass μ := by
  have h := integral_mono (row_integrable μ K x) (integrable_const (μ := μ) (1:ℝ))
    (fun y => K.le_one (x,y))
  simpa [deg,mass,smul_eq_mul] using h

lemma deg_measurable (K : Kernel X) : Measurable (deg μ K) := by
  exact K.measurable_W.stronglyMeasurable.integral_prod_right'.measurable

lemma deg_integrable (K : Kernel X) : Integrable (deg μ K) μ :=
  integrable_bounded μ (deg_measurable μ K) (deg_nonneg μ K) (deg_le_mass μ K)

lemma deg_sq_integrable (K : Kernel X) :
    Integrable (fun x => (deg μ K x)^2) μ := by
  apply integrable_bounded μ ((deg_measurable μ K).pow_const 2)
    (fun x => sq_nonneg _) (C := (mass μ)^2)
  intro x
  exact pow_le_pow_left₀ (deg_nonneg μ K x) (deg_le_mass μ K x) 2

lemma moment (K : Kernel X)
    (h : ∀ᵐ z ∂μ.prod μ, K.W z = 0 ∨ deg μ K z.1 + deg μ K z.2 ≤ mass μ) :
    2 * (∫ x, (deg μ K x)^2 ∂μ) ≤ mass μ * density μ K := by
  let F : X × X → ℝ := fun z => K.W z * deg μ K z.1
  let G : X × X → ℝ := fun z => K.W z * deg μ K z.2
  have iW : Integrable K.W (μ.prod μ) :=
    integrable_bounded _ K.measurable_W K.nonneg K.le_one
  have F_int : Integrable F (μ.prod μ) := by
    apply integrable_bounded _ (K.measurable_W.mul ((deg_measurable μ K).comp measurable_fst))
      (fun z => mul_nonneg (K.nonneg z) (deg_nonneg μ K z.1)) (C := mass μ)
    intro z
    exact (mul_le_mul_of_nonneg_right (K.le_one z) (deg_nonneg μ K z.1)).trans
      (by simpa using deg_le_mass μ K z.1)
  have G_int : Integrable G (μ.prod μ) := by
    apply integrable_bounded _ (K.measurable_W.mul ((deg_measurable μ K).comp measurable_snd))
      (fun z => mul_nonneg (K.nonneg z) (deg_nonneg μ K z.2)) (C := mass μ)
    intro z
    exact (mul_le_mul_of_nonneg_right (K.le_one z) (deg_nonneg μ K z.2)).trans
      (by simpa using deg_le_mass μ K z.2)
  have hF : (∫ z, F z ∂μ.prod μ) = ∫ x, (deg μ K x)^2 ∂μ := by
    rw [integral_prod F F_int]
    congr 1
    funext x
    change (∫ y, K.W (x,y) * deg μ K x ∂μ) = _
    rw [integral_mul_const]
    change deg μ K x * deg μ K x = (deg μ K x)^2
    ring
  have hG : (∫ z, G z ∂μ.prod μ) = ∫ z, F z ∂μ.prod μ := by
    rw [← integral_prod_swap F]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by
      rcases z with ⟨x,y⟩
      change K.W (x,y) * deg μ K y = K.W (y,x) * deg μ K y
      rw [K.symm x y])
  have hp : (∫ z, F z + G z ∂μ.prod μ) ≤ ∫ z, mass μ * K.W z ∂μ.prod μ := by
    apply integral_mono_ae (F_int.add G_int) (iW.const_mul _)
    filter_upwards [h] with z hz
    rcases hz with hz | hz
    · simp [F,G,hz]
    · have hh := mul_le_mul_of_nonneg_left hz (K.nonneg z)
      dsimp [F,G]
      nlinarith only [hh]
  rw [integral_add F_int G_int,hG,hF,integral_const_mul,integral_prod K.W iW] at hp
  change (∫ x, (deg μ K x)^2 ∂μ) + (∫ x, (deg μ K x)^2 ∂μ) ≤
    mass μ * density μ K at hp
  linarith

lemma variance (K : Kernel X) (s : ℝ) :
    0 ≤ (∫ x, (deg μ K x)^2 ∂μ) - 2*s*density μ K + mass μ*s^2 := by
  have hi₁ := deg_sq_integrable μ K
  have hi₂ := (deg_integrable μ K).const_mul (2*s)
  have he : (∫ x, (deg μ K x-s)^2 ∂μ) =
      (∫ x, (deg μ K x)^2 ∂μ) - 2*s*density μ K + mass μ*s^2 := by
    have h₀ : (fun x => (deg μ K x-s)^2) =
        fun x => (deg μ K x)^2-(2*s)*deg μ K x+s^2 := by
      funext x; ring
    have hi₃ : Integrable (fun x => (deg μ K x)^2-2*s*deg μ K x) μ :=
      hi₁.sub hi₂
    rw [h₀,integral_add hi₃ (integrable_const _),integral_sub hi₁ hi₂,
      integral_const_mul,integral_const]
    rfl
  rw [← he]
  exact integral_nonneg (fun x => sq_nonneg _)

/-- Continuous weighted Mantel given the edgewise degree inequality.
The hypothesis is obtained from the AE triangle condition in a separate lemma. -/
theorem mantel (K : Kernel X)
    (h : ∀ᵐ z ∂μ.prod μ, K.W z = 0 ∨ deg μ K z.1 + deg μ K z.2 ≤ mass μ) :
    density μ K / 2 ≤ (mass μ)^2/4 := by
  have hm0 : 0≤mass μ := measureReal_nonneg
  have hm := moment μ K h
  by_cases hz : mass μ=0
  · have h0 : density μ K=0 := by
      unfold density
      have ht : deg μ K = 0 := by
        funext x
        have h₁ := deg_nonneg μ K x
        have h₂ := deg_le_mass μ K x
        dsimp
        linarith
      rw [ht]
      simp
    simp [hz,h0]
  · have hm' : 0<mass μ := lt_of_le_of_ne hm0 (Ne.symm hz)
    have hv := variance μ K (density μ K / mass μ)
    have hc : (density μ K)^2 ≤ mass μ*(∫ x, (deg μ K x)^2 ∂μ) := by
      have he : 2*(density μ K/mass μ)*density μ K -
          mass μ*(density μ K/mass μ)^2 = (density μ K)^2/mass μ := by
        field_simp
        <;> ring
      rw [mul_comm (mass μ)]
      apply (div_le_iff₀ hm').mp
      linarith
    have hf := mul_le_mul_of_nonneg_left hm hm0
    by_contra! hn
    have hp : 0<density μ K * (density μ K - (mass μ)^2/2) := by
      apply mul_pos <;> nlinarith [sq_nonneg (mass μ)]
    nlinarith [hc]

/-- Triangle-density integrand as an explicit product kernel. -/
def triangle (K : Kernel X) (z : (X × X) × X) : ℝ :=
  K.W z.1 * K.W (z.1.1,z.2) * K.W (z.1.2,z.2)

theorem degree_sum_ae (K : Kernel X)
    (h : ∀ᵐ z ∂(μ.prod μ).prod μ, triangle K z=0) :
    ∀ᵐ z ∂μ.prod μ, K.W z=0 ∨ deg μ K z.1+deg μ K z.2≤mass μ := by
  filter_upwards [Measure.ae_ae_of_ae_prod h] with z hz
  by_cases hxy : K.W z=0
  · exact Or.inl hxy
  · right
    have hpoint : ∀ᵐ y ∂μ, K.W (z.1,y)+K.W (z.2,y)≤(1:ℝ) := by
      filter_upwards [hz] with y hy
      have hzero : K.W (z.1,y)=0 ∨ K.W (z.2,y)=0 := by
        have hp : K.W z * K.W (z.1,y) * K.W (z.2,y)=0 := hy
        rcases mul_eq_zero.mp hp with h₁ | h₂
        · exact Or.inl ((mul_eq_zero.mp h₁).resolve_left hxy)
        · exact Or.inr h₂
      rcases hzero with h₁ | h₂
      · simpa [h₁] using K.le_one (z.2,y)
      · simpa [h₂] using K.le_one (z.1,y)
    have hi := integral_mono_ae ((row_integrable μ K z.1).add (row_integrable μ K z.2))
      (integrable_const (μ := μ) (1:ℝ)) hpoint
    rw [integral_add' (row_integrable μ K z.1) (row_integrable μ K z.2),integral_const] at hi
    simpa [deg,mass,smul_eq_mul] using hi

/-- Weighted Mantel directly from zero triangle integral. -/
theorem mantel_of_zero_triangle (K : Kernel X)
    (h : (∫ z, triangle K z ∂(μ.prod μ).prod μ)=0) :
    density μ K / 2 ≤ (mass μ)^2/4 := by
  have hmeas : Measurable (triangle K) := by
    have h₁ : Measurable (fun z : (X×X)×X => K.W z.1) :=
      K.measurable_W.comp measurable_fst
    have h₂ : Measurable (fun z : (X×X)×X => K.W (z.1.1,z.2)) :=
      K.measurable_W.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have h₃ : Measurable (fun z : (X×X)×X => K.W (z.1.2,z.2)) :=
      K.measurable_W.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    exact (h₁.mul h₂).mul h₃
  have hn (z : (X×X)×X) : 0≤triangle K z :=
    mul_nonneg (mul_nonneg (K.nonneg _) (K.nonneg _)) (K.nonneg _)
  have h1 (z : (X×X)×X) : triangle K z≤1 := by
    unfold triangle
    have hf : K.W z.1 * K.W (z.1.1,z.2) ≤ 1 := by
      exact mul_le_one₀ (K.le_one _) (K.nonneg _) (K.le_one _)
    exact mul_le_one₀ hf (K.nonneg _) (K.le_one _)
  have hi := integrable_bounded ((μ.prod μ).prod μ) hmeas hn h1
  have hzero := (integral_eq_zero_iff_of_nonneg hn hi).mp h
  exact mantel μ K (degree_sum_ae μ K hzero)

/-- Taking any finite absolutely continuous submeasure preserves the
triangle-free hypothesis. This includes reweighting by a fractional half. -/
theorem mantel_submeasure {ν : Measure X} [IsFiniteMeasure ν]
    (hν : ν ≪ μ) (K : Kernel X)
    (h : ∀ᵐ z ∂(μ.prod μ).prod μ, triangle K z=0) :
    density ν K / 2 ≤ (mass ν)^2/4 := by
  have ha := (hν.prod hν).prod hν
  exact mantel ν K (degree_sum_ae ν K (h.filter_mono ha.ae_le))

#print axioms mantel_of_zero_triangle
#print axioms mantel_submeasure
end SparseHalfGraphon
