import AnchorKernelJoin

open Set MeasureTheory SparseHalfGraphon
namespace SparseHalfCountableEndpoint
variable {X : Type*} [MeasurableSpace X]
variable (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- A binary profile on an outside set gives its exact contribution to
the anchor load after any constant fractional allocation on that set. -/
theorem load_rect_single (K : Kernel X) (P S : Set X) (hP : MeasurableSet P)
    (q : ℝ) (q0 : 0≤q) (qc : q≤μ.real P)
    (h : ∀ᵐ z ∂ν.prod (μ.restrict P),
      K.W z=S.indicator (fun _ => (1:ℝ)) z.1) :
    ∀ᵐ x ∂ν, load μ K (allocSet μ P q) x=S.indicator (fun _=>q) x := by
  filter_upwards [Measure.ae_ae_of_ae_prod h] with x hx
  have fac (y : X) : allocSet μ P q y*K.W (x,y)=
      P.indicator (fun y => (q/μ.real P)*K.W (x,y)) y := by
    by_cases hy : y∈P <;> simp [allocSet,hy]
  unfold load
  simp only [fac]
  rw [integral_indicator hP]
  have eq : ∫ y in P,(q/μ.real P)*K.W (x,y) ∂μ =
      ∫ y in P,(q/μ.real P)*S.indicator (fun _ => (1:ℝ)) x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hx] with y hy
    rw [hy]
  rw [eq,setIntegral_const,smul_eq_mul]
  by_cases xs : x∈S
  · rw [indicator_of_mem xs,indicator_of_mem xs,mul_one]
    by_cases p0 : μ.real P=0
    · have eq : q=0 := le_antisymm (p0 ▸ qc) q0
      simp [eq]
    · rw [mul_comm,div_mul_cancel₀ _ p0]
  · simp [indicator_of_notMem xs]

/-- Exact additive anchor load of a finite collection of outside
rectangles, with fractional allocations within the chosen pools. -/
theorem load_rect_sum {J : Type*} [Fintype J] (K : Kernel X) (P S : J→Set X)
    (hP : ∀ j, MeasurableSet (P j)) (q : J→ℝ)
    (hq : ∀ j,0≤q j ∧ q j≤μ.real (P j))
    (hk : ∀ j, ∀ᵐ z ∂ν.prod (μ.restrict (P j)),
      K.W z=(S j).indicator (fun _ => (1:ℝ)) z.1) :
    ∀ᵐ x ∂ν, load μ K (fun y => ∑ j, allocSet μ (P j) (q j) y) x =
      ∑ j,(S j).indicator (fun _ => q j) x := by
  have aeall := ae_all_iff.2 (fun j =>
    load_rect_single μ ν K (P j) (S j) (hP j) (q j) (hq j).1 (hq j).2 (hk j))
  filter_upwards [aeall] with x hx
  have i (j : J) : Integrable (fun y => allocSet μ (P j) (q j) y*K.W (x,y)) μ := by
    have hb := allocSet_bmeas μ (P j) (hP j) (q j) (hq j).1 (hq j).2
    have hr := BMeas.of_unit (rowMeasurable K x) (fun _=>K.nonneg _) (fun _=>K.le_one _)
    exact bMeas_integrable μ (hb.mul hr)
  unfold load
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ (fun j _ => i j)]
  exact Finset.sum_congr rfl (fun j _ => hx j)

#print axioms load_rect_single
#print axioms load_rect_sum
end SparseHalfCountableEndpoint
