import BlockMeans

open MeasureTheory Set Function
namespace SparseHalfGraphon
variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace ι] [MeasurableSpace κ]
  [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]

/-- Exact Pythagorean energy increment on a finite block refinement. -/
theorem refinement_energy (c : X→ι) (d : X→κ) (p : κ→ι)
    (hc : Measurable c) (hd : Measurable d) (href : ∀ x, c x=p (d x))
    (W : X→ℝ) (hW : BMeas W) :
    (∫ x, (meanBlock μ d W x)^2 ∂μ)-(∫ x, (meanBlock μ c W x)^2 ∂μ)=
      ∫ x, (meanBlock μ d W x-meanBlock μ c W x)^2 ∂μ := by
  let C := meanBlock μ c W
  let D := meanBlock μ d W
  have bC : BMeas C := block_bmeas μ c hc W
  have bD : BMeas D := block_bmeas μ d hd W
  have h₁ : (∫ x, (W x-C x)*C x ∂μ)=0 :=
    mean_orthogonal μ c hc W hW (meanCell μ c W)
  have h₂ : (∫ x, (W x-D x)*C x ∂μ)=0 := by
    have h := mean_orthogonal μ d hd W hW (fun j => meanCell μ c W (p j))
    simpa only [C,D,meanBlock,href] using h
  have ho : (∫ x, (D x-C x)*C x ∂μ)=0 := by
    have he : (fun x => (D x-C x)*C x) =
        fun x => (W x-C x)*C x-(W x-D x)*C x := by funext x; ring
    have i₁ : Integrable (fun x => (W x-C x)*C x) μ :=
      bMeas_integrable μ ((hW.sub bC).mul bC)
    have i₂ : Integrable (fun x => (W x-D x)*C x) μ :=
      bMeas_integrable μ ((hW.sub bD).mul bC)
    rw [he,integral_sub i₁ i₂,h₁,h₂,sub_zero]
  have he : (fun x => (D x-C x)^2) =
      fun x => (D x^2-C x^2)-2*((D x-C x)*C x) := by funext x; ring
  change (∫ x, D x^2 ∂μ)-(∫ x, C x^2 ∂μ)=∫ x, (D x-C x)^2 ∂μ
  have i₁ := bMeas_integrable μ bD.sq
  have i₂ := bMeas_integrable μ bC.sq
  have i₃ : Integrable (fun x => D x^2-C x^2) μ := i₁.sub i₂
  have i₄ : Integrable (fun x => 2*((D x-C x)*C x)) μ :=
    (bMeas_integrable μ ((bD.sub bC).mul bC)).const_mul _
  rw [he,integral_sub i₃ i₄,integral_sub i₁ i₂,integral_const_mul,ho,mul_zero,sub_zero]

/-- A second moment lower bound from any bounded signed test. -/
theorem test_second_moment (f g : X→ℝ) (hf : BMeas f) (hg : BMeas g)
    (hg₂ : (∫ x, g x^2 ∂μ)≤1) :
    (∫ x, f x*g x ∂μ)^2≤∫ x, f x^2 ∂μ := by
  let q := ∫ x, f x*g x ∂μ
  have hpos : 0≤∫ x, (f x-q*g x)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have he : (fun x => (f x-q*g x)^2) =
      fun x => (f x^2-(2*q)*(f x*g x))+q^2*(g x^2) := by funext x; ring
  have i₁ := bMeas_integrable μ hf.sq
  have i₂ : Integrable (fun x => (2*q)*(f x*g x)) μ :=
    (bMeas_integrable μ (hf.mul hg)).const_mul _
  have i₃ : Integrable (fun x => f x^2-(2*q)*(f x*g x)) μ := i₁.sub i₂
  have i₄ : Integrable (fun x => q^2*(g x^2)) μ := (bMeas_integrable μ hg.sq).const_mul _
  rw [he,integral_add i₃ i₄,integral_sub i₁ i₂,integral_const_mul,integral_const_mul] at hpos
  change 0≤(∫ x, f x^2 ∂μ)-(2*q)*q+q^2*(∫ x, g x^2 ∂μ) at hpos
  have h := mul_le_mul_of_nonneg_left hg₂ (sq_nonneg q)
  change q^2≤∫ x, f x^2 ∂μ
  nlinarith only [h,hpos]

/-- A mean refinement that represents a cut witness gains its squared
cut error in energy; can be iterated in a weak regularity proof. -/
theorem refinement_witness (c : X→ι) (d : X→κ) (p : κ→ι)
    (hc : Measurable c) (hd : Measurable d) (href : ∀ x, c x=p (d x))
    (W : X→ℝ) (hW : BMeas W) (v : κ→ℝ)
    (hV : (∫ x, (v (d x))^2 ∂μ)≤1) :
    (∫ x, (W x-meanBlock μ c W x)*v (d x) ∂μ)^2 ≤
      (∫ x, (meanBlock μ d W x)^2 ∂μ)-(∫ x, (meanBlock μ c W x)^2 ∂μ) := by
  let C := meanBlock μ c W
  let D := meanBlock μ d W
  let g : X→ℝ := v ∘ d
  have bC : BMeas C := block_bmeas μ c hc W
  have bD : BMeas D := block_bmeas μ d hd W
  have bG : BMeas g := bmeas_comp_finite d hd v
  have hz : (∫ x, (W x-D x)*g x ∂μ)=0 := mean_orthogonal μ d hd W hW v
  have heq : (∫ x, (W x-C x)*g x ∂μ)=∫ x, (D x-C x)*g x ∂μ := by
    have he : (fun x => (W x-C x)*g x) = fun x => (W x-D x)*g x+(D x-C x)*g x := by
      funext x; ring
    have i₁ : Integrable (fun x => (W x-D x)*g x) μ :=
      bMeas_integrable μ ((hW.sub bD).mul bG)
    have i₂ : Integrable (fun x => (D x-C x)*g x) μ :=
      bMeas_integrable μ ((bD.sub bC).mul bG)
    rw [he,integral_add i₁ i₂,hz,zero_add]
  change (∫ x, (W x-C x)*g x ∂μ)^2≤_
  rw [heq,refinement_energy μ c d p hc hd href W hW]
  exact test_second_moment μ (D-C) g (bD.sub bC) bG hV

#print axioms refinement_energy
#print axioms refinement_witness
end SparseHalfGraphon
