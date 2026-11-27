import ComplementRowsAE

open MeasureTheory Set
open scoped ENNReal

namespace SparseHalfGraphon
variable {X : Type*} [MeasurableSpace X]

lemma triangle_measurable (K : Kernel X) : Measurable (triangle K) := by
  exact ((K.measurable_W.comp measurable_fst).mul
    (K.measurable_W.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))).mul
    (K.measurable_W.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

/-- For a triangle-free graphon, almost every weighted neighborhood
is independent. D is any residual vertex weight, and need not be binary. -/
theorem neighborhood_allocation_energy_zero (μ : Measure X) [IsFiniteMeasure μ]
    (K : Kernel X) (D : X→ℝ)
    (htri : ∀ᵐ z ∂(μ.prod μ).prod μ, triangle K z=0) :
    ∀ᵐ v ∂μ, (∫ z, K.W z*(D z.1*K.W (v,z.1))*(D z.2*K.W (v,z.2)) ∂μ.prod μ)=0 := by
  have hp : MeasurableSet {z | triangle K z=0} :=
    measurableSet_eq_fun (triangle_measurable K) measurable_const
  have hh : ∀ᵐ v ∂μ, ∀ᵐ z ∂μ.prod μ, triangle K (z,v)=0 :=
    (Measure.ae_ae_comm hp).mp (Measure.ae_ae_of_ae_prod htri)
  filter_upwards [hh] with v hv
  have hi : (∫ z, K.W z*(D z.1*K.W (v,z.1))*(D z.2*K.W (v,z.2)) ∂μ.prod μ) =
      ∫ _ : X×X, (0:ℝ) ∂μ.prod μ := by
    apply integral_congr_ae
    filter_upwards [hv] with z hz
    calc
      K.W z*(D z.1*K.W (v,z.1))*(D z.2*K.W (v,z.2)) =
        (D z.1*D z.2)*triangle K (z,v) := by
          unfold triangle
          rw [K.symm z.1 v, K.symm z.2 v]
          ring
      _ = 0 := by rw [hz,mul_zero]
  rw [hi,integral_zero]

#print axioms neighborhood_allocation_energy_zero
end SparseHalfGraphon
