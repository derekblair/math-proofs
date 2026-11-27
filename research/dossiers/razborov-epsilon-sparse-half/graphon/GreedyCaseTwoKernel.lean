import GreedyMoments
import GraphonCaseTwo

open Set MeasureTheory Function
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- Razborov's Case 2 bound on the actual kernel and its two marks,
before specializing the growing mass b to the endpoint. -/
theorem greedy_kernel_case_two (K : Kernel X) (a D : X→ℝ)
    (ha : Measurable a) (hD : Measurable D)
    (ha0 : ∀ x,0≤a x) (hD0 : ∀ x,0≤D x) (hcap : ∀ x,a x+D x≤1)
    (A b c : ℝ) (hAl : A<1/2) (hb : 0<b)
    (hA : (∫ x,a x ∂μ)=b) (hMassD : (∫ x,D x ∂μ)=1-A-b)
    (hAA : energyPair μ K a a/2≤(1/2-A)*(b-A))
    (htri : ∀ᵐ z ∂(μ.prod μ).prod μ, triangle K z=0)
    (hdeg : ∀ x,0<D x → 1/2-A≤deg (reweight μ a) K x ∧ deg (reweight μ a) K x≤b/2)
    (hLoad : ∀ᵐ v ∂reweight μ a, load μ K D v≤1/2-b)
    (hc : (∫ x,D x*deg (reweight μ a) K x ∂μ)=c/2) :
    beta μ K≤greedyCaseTwo A b c := by
  let ν := reweight μ a
  have ha1 (x) : a x≤1 := by linarith [hcap x,hD0 x]
  have hD1 (x) : D x≤1 := by linarith [hcap x,ha0 x]
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le μ (reweight_le μ a ha1)
  have ba := BMeas.of_unit ha ha0 ha1
  have bD := BMeas.of_unit hD hD0 hD1
  have hν : mass ν=b := (reweight_mass μ a ha ha0).trans hA
  apply greedy_average ν A b c (beta μ K) hb hν (load μ K D) (rootCross μ ν K D)
    (load_bmeas μ K bD) (load_bmeas μ K (bD.mul (deg_bmeas ν K)))
    ((load_marginal μ ν K D bD).trans hc)
    (greedy_cross_moment μ ν K D bD hD0 A b c hMassD hc hdeg)
  have hee := (neighborhood_allocation_energy_zero μ K D htri).filter_mono (reweight_ac μ a).ae_le
  filter_upwards [hLoad,hee] with v hv heV
  let e : X→ℝ := fun x => D x*K.W (v,x)
  let f : X→ℝ := D-e
  have be : BMeas e :=
    bD.mul (BMeas.of_unit (rowMeasurable K v) (fun x => K.nonneg _) (fun x => K.le_one _))
  have bf : BMeas f := bD.sub be
  have he0 (x : X) : 0≤e x := mul_nonneg (hD0 x) (K.nonneg _)
  have heD (x : X) : e x≤D x := by
    exact (mul_le_mul_of_nonneg_left (K.le_one (v,x)) (hD0 x)).trans_eq (mul_one _)
  have hf0 (x : X) : 0≤f x := sub_nonneg.mpr (heD x)
  have hEF : (∫ x, e x ∂μ)+(∫ x, f x ∂μ)=1-A-b := by
    change (∫ x, e x ∂μ)+(∫ x, (D-e) x ∂μ)=_
    rw [integral_sub' (bMeas_integrable μ bD) (bMeas_integrable μ be),hMassD]
    ring
  have he0cost : energyPair μ K e e=0 := by
    unfold energyPair
    convert heV using 1
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by dsimp [e]; ring)
  have hAF : energyPair μ K a f≤(b/2)*(∫ x, f x ∂μ) := by
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
      change f x*deg ν K x≤(b/2)*f x
      rw [mul_comm (b/2) (f x)]
      exact mul_le_mul_of_nonneg_left hh (hf0 x)
  have hlocal := greedy_local_half μ K a e f ba be bf ha0 he0 hf0
    (fun x => by change a x+e x+(D x-e x)≤1; linarith [hcap x])
    b A hAl hA hEF hv he0cost hAF htri

  have hrc : energyPair μ K a e = rootCross μ ν K D v := by
    rw [energy_row μ K a e ba be]
    simp only [weightedDegree_eq_reweight μ K a ha ha0]
    unfold rootCross load
    apply integral_congr_ae
    exact ae_of_all _ (fun x=>by dsimp [e]; ring)
  dsimp at hlocal
  rw [hrc] at hlocal
  have hE : (∫ x,e x ∂μ)=load μ K D v := rfl
  rw [hE] at hlocal
  unfold greedyLocalPoly
  nlinarith only [hlocal,hAA]

#print axioms greedy_kernel_case_two
end SparseHalfGraphon
