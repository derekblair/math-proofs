import AlignedFamilyBounds

open Set MeasureTheory Function Filter Topology
open scoped ENNReal
namespace SparseHalfGraphon

/-- Degree upper caps survive convergence in cut, even though
independence upper caps do not in general. -/
theorem cut_limit_degree_cap {Z : ℕ→Type*} [∀ k, MeasurableSpace (Z k)]
    {Y : Type*} [MeasurableSpace Y]
    (μ : ∀ k, Measure (Z k)) [∀ k, IsFiniteMeasure (μ k)]
    (ν : Measure Y) [IsFiniteMeasure ν] (hν : mass ν=1)
    (W : ∀ k, Kernel (Z k)) (L : Kernel Y)
    (b : ℝ) (B : ℕ→ℝ) (hB : Tendsto B atTop (𝓝 b))
    (hdeg : ∀ k, ∀ᵐ x ∂μ k, deg (μ k) (W k) x≤B k)
    (hc : ∀ ε>0, ∀ᶠ k in atTop, ∃ π : Measure (Z k×Y),
      MeasurePreserving Prod.fst π (μ k) ∧ MeasurePreserving Prod.snd π ν ∧
      π univ = 1 ∧ CutBound π (pullKernel (W k) Prod.fst measurable_fst)
        (pullKernel L Prod.snd measurable_snd) ε) :
    ∀ᵐ y ∂ν, deg ν L y≤b := by
  apply aligned_family_upper_ae ν hν (deg ν L) (deg_bmeas ν L) b
    (fun k => deg (μ k) (W k)) (fun k=>deg_measurable (μ k) (W k))
  intro ε he
  have ee : 0<ε/2 := by positivity
  obtain ⟨k,⟨π,hf,hs,hπ,hcut⟩,hk⟩ :=
    ((hc (ε/2) ee).and (Metric.tendsto_nhds.mp hB ε he)).exists
  have : IsFiniteMeasure π := ⟨by rw [hπ]; exact ENNReal.one_lt_top⟩
  refine ⟨k,π,hs,?_,?_,?_⟩
  · have hh := hf.quasiMeasurePreserving.ae (hdeg k)
    rw [Real.dist_eq] at hk
    filter_upwards [hh] with z hz
    change deg (μ k) (W k) z.1 ≤ B k at hz
    linarith [le_abs_self (B k-b)]
  · exact (bMeas_integrable π ((bmeas_comp_meas (deg_bmeas (μ k) (W k)) measurable_fst).sub
      (bmeas_comp_meas (deg_bmeas ν L) measurable_snd))).abs
  · have h := cut_degree_L1 π _ _ (ε/2) hcut univ MeasurableSet.univ
    have hF (z : Z k×Y) := degree_pull_restricted hf (S:=univ) MeasurableSet.univ (W k) z
    have hS (z : Z k×Y) := degree_pull_restricted hs (S:=univ) MeasurableSet.univ L z
    simp only [preimage_univ, Measure.restrict_univ] at h hF hS
    simp_rw [hF,hS] at h
    exact h.trans (by ring_nf; rfl)

#print axioms cut_limit_degree_cap
end SparseHalfGraphon
