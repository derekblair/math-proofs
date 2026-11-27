import RectangleJoin

open Set MeasureTheory SparseHalfGraphon
namespace SparseHalfCountableEndpoint
variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

/-- If a half is tight in the completed kernel and takes both cells
of an incomplete allowed rectangle, it is strict in the original.
The missing-edge hypothesis is genuinely a.e., not a pointwise defect. -/
theorem strict_of_missing_rectangle (K J : Kernel X) (H : Half μ)
    (S T : Set X) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (major : ∀ᵐ z ∂μ.prod μ, K.W z≤J.W z)
    (tight : halfEnergy μ J H≤1/50)
    (fS : ∀ x∈S, H.f x=1) (fT : ∀ x∈T, H.f x=1)
    (full : ∀ᵐ z ∂(μ.restrict S).prod (μ.restrict T), J.W z=1)
    (missing : ¬ ∀ᵐ z ∂(μ.restrict S).prod (μ.restrict T), K.W z=1) :
    halfEnergy μ K H<1/50 := by
  have hf := BMeas.of_unit H.measurable_f H.nn H.le_one
  let k := fun z : X×X => H.f z.1*H.f z.2*K.W z
  let j := fun z : X×X => H.f z.1*H.f z.2*J.W z
  have ki : Integrable k (μ.prod μ) := energy_integrable μ K hf hf
  have ji : Integrable j (μ.prod μ) := energy_integrable μ J hf hf
  have le : k≤ᵐ[μ.prod μ] j := by
    filter_upwards [major] with z hz
    exact mul_le_mul_of_nonneg_left hz (mul_nonneg (H.nn _) (H.nn _))
  have s : (∫ z,k z ∂μ.prod μ)<∫ z,j z ∂μ.prod μ := by
    apply lt_of_le_of_ne (integral_mono_ae ki ji le)
    intro eq
    have heq := (integral_eq_iff_of_ae_le ki ji le).1 eq
    have hres : ∀ᵐ z ∂(μ.restrict S).prod (μ.restrict T), k z=j z := by
      rw [Measure.prod_restrict]
      exact ae_mono Measure.restrict_le_self heq
    have hmem : ∀ᵐ z ∂(μ.restrict S).prod (μ.restrict T), z.1∈S ∧ z.2∈T := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (hS.prod hT)
    apply missing
    filter_upwards [hres,hmem,full] with z eq ⟨hs,ht⟩ one
    simpa [k,j,fS _ hs,fT _ ht,one] using eq
  rw [halfEnergy_as_pair] at tight ⊢
  change (∫ z,k z ∂μ.prod μ)/2<1/50
  change (∫ z,j z ∂μ.prod μ)/2≤1/50 at tight
  linarith

theorem strict_of_missing_rectangle_pos (K J : Kernel X) (H : Half μ)
    (S T : Set X) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (major : ∀ᵐ z ∂μ.prod μ, K.W z≤J.W z)
    (tight : halfEnergy μ J H≤1/50)
    (fS : ∀ x∈S, 0<H.f x) (fT : ∀ x∈T, 0<H.f x)
    (full : ∀ᵐ z ∂(μ.restrict S).prod (μ.restrict T), J.W z=1)
    (missing : ¬ ∀ᵐ z ∂(μ.restrict S).prod (μ.restrict T), K.W z=1) :
    halfEnergy μ K H<1/50 := by
  have hf := BMeas.of_unit H.measurable_f H.nn H.le_one
  let k := fun z : X×X => H.f z.1*H.f z.2*K.W z
  let j := fun z : X×X => H.f z.1*H.f z.2*J.W z
  have ki : Integrable k (μ.prod μ) := energy_integrable μ K hf hf
  have ji : Integrable j (μ.prod μ) := energy_integrable μ J hf hf
  have le : k≤ᵐ[μ.prod μ] j := by
    filter_upwards [major] with z hz
    exact mul_le_mul_of_nonneg_left hz (mul_nonneg (H.nn _) (H.nn _))
  have s : (∫ z,k z ∂μ.prod μ)<∫ z,j z ∂μ.prod μ := by
    apply lt_of_le_of_ne (integral_mono_ae ki ji le)
    intro eq
    have heq := (integral_eq_iff_of_ae_le ki ji le).1 eq
    have hres : ∀ᵐ z ∂(μ.restrict S).prod (μ.restrict T), k z=j z := by
      rw [Measure.prod_restrict]
      exact ae_mono Measure.restrict_le_self heq
    have hmem : ∀ᵐ z ∂(μ.restrict S).prod (μ.restrict T), z.1∈S ∧ z.2∈T := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (hS.prod hT)
    apply missing
    filter_upwards [hres,hmem,full] with z eq ⟨hs,ht⟩ one
    change H.f z.1*H.f z.2*K.W z=H.f z.1*H.f z.2*J.W z at eq
    have a : 0<H.f z.1*H.f z.2 := mul_pos (fS _ hs) (fT _ ht)
    have b := mul_left_cancel₀ a.ne' eq
    simpa only [one] using b
  rw [halfEnergy_as_pair] at tight ⊢
  change (∫ z,k z ∂μ.prod μ)/2<1/50
  change (∫ z,j z ∂μ.prod μ)/2≤1/50 at tight
  linarith


#print axioms strict_of_missing_rectangle_pos
#print axioms strict_of_missing_rectangle
end SparseHalfCountableEndpoint
