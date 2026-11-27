import AlignedLimits

open Set MeasureTheory Function
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- The normalized triangle count vanishes exactly when the triangle
integrand vanishes almost everywhere. -/
theorem zero_triangle_iff_ae (K : Kernel X) :
    t3 μ K K K = 0 ↔ ∀ᵐ z ∂(μ.prod μ).prod μ, triangle K z = 0 := by
  have h₀ : ∀ z, 0 ≤ triangle K z := by
    rintro ⟨⟨x,y⟩,z⟩
    unfold triangle
    exact mul_nonneg (mul_nonneg (K.nonneg _) (K.nonneg _)) (K.nonneg _)
  have h₁ : ∀ z, triangle K z ≤ 1 := by
    rintro ⟨⟨x,y⟩,z⟩
    unfold triangle
    have hp : K.W (x,y)*K.W (x,z) ≤ 1 := by
      calc
        _ ≤ 1*K.W (x,z) := mul_le_mul_of_nonneg_right (K.le_one _) (K.nonneg _)
        _ ≤ 1 := by simpa only [one_mul] using K.le_one (x,z)
    calc
      _ ≤ 1*K.W (y,z) := mul_le_mul_of_nonneg_right hp (K.nonneg _)
      _ ≤ 1 := by simpa only [one_mul] using K.le_one (y,z)
  have hi := integrable_bounded ((μ.prod μ).prod μ) (triangle_measurable K) h₀ h₁
  change (∫ z, triangle K z ∂(μ.prod μ).prod μ) = 0 ↔ _
  exact integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ h₀) hi

#print axioms zero_triangle_iff_ae
end SparseHalfGraphon
