import GraphonCaseTwoMarginals

open MeasureTheory Set
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

lemma weightedDegree_eq_reweight (K : Kernel X) (a : X→ℝ) (ha : Measurable a)
    (ha0 : ∀ x, 0≤a x) (y : X) :
    weightedDegree μ K a y=deg (reweight μ a) K y := by
  unfold weightedDegree deg
  rw [reweight_integral μ a ha ha0]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by change a x*K.W (x,y)=a x*K.W (y,x); rw [K.symm y x])

/-- Exact fractional Case 2 at the endpoint, on an arbitrary finite measure
space. The mark a and the allocation D may be fractional. -/
theorem graphon_case_two (K : Kernel X) (a D : X→ℝ)
    (ha : Measurable a) (hD : Measurable D)
    (ha0 : ∀ x, 0≤a x) (hD0 : ∀ x, 0≤D x)
    (hcap : ∀ x, a x+D x≤1)
    (hA : (∫ x, a x ∂μ)=2/5) (hMassD : (∫ x, D x ∂μ)=1/5)
    (hAA : energyPair μ K a a=0)
    (htri : ∀ᵐ z ∂(μ.prod μ).prod μ, triangle K z=0)
    (hdeg : ∀ x, 0<D x →
        1/10≤deg (reweight μ a) K x ∧ deg (reweight μ a) K x≤1/5)
    (hload : ∀ᵐ v ∂reweight μ a, load μ K D v≤1/10)
    (hZ : 0<defMass μ (reweight μ a) K D) :
    beta μ K<1/50 := by
  let ν := reweight μ a
  have ha1 (x : X) : a x≤1 := by linarith [hcap x,hD0 x]
  have hD1 (x : X) : D x≤1 := by linarith [hcap x,ha0 x]
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le μ (reweight_le μ a ha1)
  have ba := BMeas.of_unit ha ha0 ha1
  have bD := BMeas.of_unit hD hD0 hD1
  have hν : mass ν=2/5 := (reweight_mass μ a ha ha0).trans hA
  have hδ : BMeas (deficit ν K) := (BMeas.const _).sub (deg_bmeas ν K)
  have bR : BMeas (rowDef μ ν K D) := load_bmeas μ K (bD.mul hδ)
  have bH : BMeas (rem μ K D) := (BMeas.const _).sub (load_bmeas μ K bD)
  refine case_two_average ν (beta μ K) (defMass μ ν K D) (rem μ K D)
    (rowDef μ ν K D) hν bH bR hZ
    (rem_exact μ ν K D bD hν hMassD) ?_ ?_
  · rw [row_def_integral μ ν K D bD]
    have hi₁ : Integrable (fun x => D x*(deficit ν K x)^2) μ :=
      bMeas_integrable μ (bD.mul hδ.sq)
    have hi₂ : Integrable (fun x => D x*deficit ν K x*(1/10)) μ :=
      (bMeas_integrable μ (bD.mul hδ)).mul_const _
    have hi := integral_mono hi₁ hi₂ (fun x => by
      by_cases h0 : D x=0
      · simp [h0]
      · have hh := hdeg x (lt_of_le_of_ne (hD0 x) (Ne.symm h0))
        have hj : 0≤deficit ν K x := by unfold deficit; linarith [hh.2]
        have hv : deficit ν K x≤1/10 := by unfold deficit; linarith [hh.1]
        have hp := mul_nonneg (hD0 x) (mul_nonneg hj (sub_nonneg.mpr hv))
        nlinarith only [hp])
    rw [integral_mul_const] at hi
    change (∫ x, D x*(deficit ν K x)^2 ∂μ)≤defMass μ ν K D*(1/10) at hi
    linarith
  · have hee := (neighborhood_allocation_energy_zero μ K D htri).filter_mono
      (reweight_ac μ a).ae_le
    filter_upwards [hload,hee] with v hv heV
    let e : X→ℝ := fun x => D x*K.W (v,x)
    let f : X→ℝ := D-e
    have be : BMeas e :=
      bD.mul (BMeas.of_unit (rowMeasurable K v) (fun x => K.nonneg _) (fun x => K.le_one _))
    have bf : BMeas f := bD.sub be
    have he0 (x : X) : 0≤e x := mul_nonneg (hD0 x) (K.nonneg _)
    have heD (x : X) : e x≤D x := by
      exact (mul_le_mul_of_nonneg_left (K.le_one (v,x)) (hD0 x)).trans_eq (mul_one _)
    have hf0 (x : X) : 0≤f x := sub_nonneg.mpr (heD x)
    have hEF : (∫ x, e x ∂μ)+(∫ x, f x ∂μ)=1/5 := by
      change (∫ x, e x ∂μ)+(∫ x, (D-e) x ∂μ)=_
      rw [integral_sub' (bMeas_integrable μ bD) (bMeas_integrable μ be),hMassD]
      ring
    have he0cost : energyPair μ K e e=0 := by
      unfold energyPair
      convert heV using 1
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by dsimp [e]; ring)
    have hAF : energyPair μ K a f≤(1/5)*(∫ x, f x ∂μ) := by
      rw [energy_row μ K a f ba bf,← integral_const_mul]
      simp only [weightedDegree_eq_reweight μ K a ha ha0]
      have hi₁ : Integrable (fun x => f x*deg ν K x) μ :=
        bMeas_integrable μ (bf.mul (deg_bmeas ν K))
      apply integral_mono hi₁ ((bMeas_integrable μ bf).const_mul _)
      intro x
      by_cases h0 : f x=0
      · simp [h0]
      · have hDx : 0<D x := by
          have hF : f x=D x-e x := rfl
          have hfp := lt_of_le_of_ne (hf0 x) (Ne.symm h0)
          linarith [he0 x]
        have hh := (hdeg x hDx).2
        change f x*deg ν K x≤(1/5)*f x
        rw [mul_comm (1/5) (f x)]
        exact mul_le_mul_of_nonneg_left hh (hf0 x)
    have hlocal := local_fractional_half μ K a e f ba be bf ha0 he0 hf0
      (fun x => by change a x+e x+(D x-e x)≤1; linarith [hcap x])
      hA hEF hv hAA he0cost hAF htri
    have hrow : (1/5)*(∫ x, e x ∂μ)-energyPair μ K a e=rowDef μ ν K D v := by
      rw [energy_row μ K a e ba be,← integral_const_mul]
      simp only [weightedDegree_eq_reweight μ K a ha ha0]
      have hi₁ : Integrable (fun x => (1/5)*e x) μ := (bMeas_integrable μ be).const_mul _
      have hi₂ : Integrable (fun x => e x*deg ν K x) μ :=
        bMeas_integrable μ (be.mul (deg_bmeas ν K))
      rw [← integral_sub hi₁ hi₂]
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        change (1/5)*e x-e x*deg ν K x=(D x*deficit ν K x)*K.W (v,x)
        unfold deficit; dsimp [e]; ring)
    dsimp only at hlocal
    rw [hrow] at hlocal
    exact hlocal

#print axioms graphon_case_two
end SparseHalfGraphon
