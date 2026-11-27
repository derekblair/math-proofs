import CutFractionalTest

open MeasureTheory Set
open scoped ENNReal

namespace SparseHalfGraphon
variable {X : Type*} [MeasurableSpace X]

noncomputable def gapW (K J : Kernel X) (z : X×X) := K.W z-J.W z

lemma gapW_bound (K J : Kernel X) (z : X×X) :
    |gapW K J z|≤1 := by
  rw [abs_le]; unfold gapW
  constructor <;> linarith [K.nonneg z,K.le_one z,J.nonneg z,J.le_one z]

/-- The rectangle control gives the same bound against a product of
any two fractional test functions. -/
theorem cut_product_test (μ : Measure X) [IsFiniteMeasure μ]
    (K J : Kernel X) (ε : ℝ) (hcut : CutBound μ K J ε)
    (f g : X→ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf₀ : ∀ x, 0≤f x) (hf₁ : ∀ x, f x≤1)
    (hg₀ : ∀ x, 0≤g x) (hg₁ : ∀ x, g x≤1) :
    |∫ y, (∫ x, gapW K J (x,y)*f x ∂μ)*g y ∂μ|≤ε := by
  let k := gapW K J
  have hk : Measurable k := K.measurable_W.sub J.measurable_W
  have hsum (z : X×X) : |k z*f z.1|≤1 := by
    rw [abs_mul,abs_of_nonneg (hf₀ _)]
    exact (mul_le_mul_of_nonneg_right (gapW_bound K J z) (hf₀ _)).trans (by simp [hf₁ _])
  let F : X×X→ℝ := fun z => k z*f z.1
  have hF : Measurable F := hk.mul (hf.comp measurable_fst)
  let v : X→ℝ := fun y => ∫ x, F (x,y) ∂μ
  have hv : Measurable v := hF.stronglyMeasurable.integral_prod_left'.measurable
  have fI (ν ν' : Measure X) [IsFiniteMeasure ν] [IsFiniteMeasure ν'] :
      Integrable F (ν.prod ν') :=
    Integrable.of_bound hF.aestronglyMeasurable 1
      (ae_of_all _ (fun z => by simpa [Real.norm_eq_abs,F] using hsum z))
  have kRow (ν : Measure X) [IsFiniteMeasure ν] (x : X) :
      Integrable (fun y => k (x,y)) ν :=
    (row_integrable ν K x).sub (row_integrable ν J x)
  have hB (y : X) : |v y|≤mass μ := by
    calc
      |v y| ≤ ∫ x, |F (x,y)| ∂μ := by
        unfold v
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (μ:=μ) (f:=fun x => F (x,y)))
      _ ≤ mass μ := by
        have hi : Integrable (fun x => F (x,y)) μ :=
          Integrable.of_bound
            (hF.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable 1
            (ae_of_all _ (fun x => by simpa [Real.norm_eq_abs,F] using hsum (x,y)))
        have h := integral_mono hi.abs (integrable_const (μ := μ) (1:ℝ))
          (fun x => hsum (x,y))
        simpa [mass,smul_eq_mul] using h
  change |∫ y, v y*g y ∂μ|≤ε
  apply bounded_test μ v g hv hg (mass μ) ε hB hg₀ hg₁
  intro T hT
  let ν := μ.restrict T
  let u : X→ℝ := fun x => ∫ y, k (x,y) ∂ν
  have hU : Measurable u := hk.stronglyMeasurable.integral_prod_right'.measurable
  have hUb (x : X) : |u x|≤mass ν := by
    calc
      |u x| ≤ ∫ y, |k (x,y)| ∂ν := by
        unfold u
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (μ:=ν) (f:=fun y=>k (x,y)))
      _ ≤ mass ν := by
        have h := integral_mono (kRow ν x).abs (integrable_const (μ := ν) (1:ℝ))
          (fun y => gapW_bound K J (x,y))
        simpa [mass,smul_eq_mul] using h
  have he : (∫ y in T, v y ∂μ) = ∫ x, u x*f x ∂μ := by
    change (∫ y, ∫ x, F (x,y) ∂μ ∂ν) = _
    rw [← integral_prod_symm F (fI μ ν),integral_prod F (fI μ ν)]
    congr 1
    funext x
    change (∫ y, k (x,y)*f x ∂ν) = _
    rw [integral_mul_const]
  rw [he]
  apply bounded_test μ u f hU hf (mass ν) ε hUb hf₀ hf₁
  intro S hS
  exact hcut S T hS hT

#print axioms cut_product_test
end SparseHalfGraphon
