import GreedyCaseTwoKernel

open Set MeasureTheory Function
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- A root with enough eligible neighbor load gives the actual Case 1
half, using a fractional truncation that also works on atomic spaces. -/
theorem greedy_kernel_case_one (W : Kernel X) (a D : X→ℝ)
    (ha : Measurable a) (hD : Measurable D)
    (ha0 : ∀ x,0≤a x) (hD0 : ∀ x,0≤D x) (hcap : ∀ x,a x+D x≤1)
    (A b : ℝ) (hb : b≤1/2) (hA : (∫ x,a x ∂μ)=b)
    (hAA : energyPair μ W a a/2≤(1/2-A)*(b-A))
    (hdeg : ∀ x,0<D x→deg (reweight μ a) W x≤b/2)
    (v : X) (hload : 1/2-b≤load μ W D v)
    (hN : energyPair μ W (fun x=>D x*W.W (v,x)) (fun x=>D x*W.W (v,x))=0) :
    beta μ W ≤ greedyCaseOne A b := by
  have ha1 (x) : a x≤1 := by linarith [hcap x,hD0 x]
  have hD1 (x) : D x≤1 := by linarith [hcap x,ha0 x]
  have : IsFiniteMeasure (reweight μ a) := isFiniteMeasure_of_le μ (reweight_le μ a ha1)
  have ba := BMeas.of_unit ha ha0 ha1
  have bD := BMeas.of_unit hD hD0 hD1
  let F : X→ℝ := fun x => D x*W.W (v,x)
  let m := load μ W D v
  let t := (1/2-b)/m
  have hm : (∫ x,F x ∂μ)=m := rfl
  have m0 : 0≤m := (sub_nonneg.mpr hb).trans hload
  have ht0 : 0≤t := div_nonneg (sub_nonneg.mpr hb) m0
  have ht1 : t≤1 := by
    by_cases he : m=0
    · simp [t,he]
    · exact (div_le_iff₀ (lt_of_le_of_ne m0 (Ne.symm he))).mpr (by simpa using hload)
  have ht : t*m=1/2-b := by
    by_cases he : m=0
    · have hz : 1/2-b=0 := le_antisymm (he ▸ hload) (sub_nonneg.mpr hb)
      rw [he,mul_zero,hz]
    · exact div_mul_cancel₀ _ he
  have f0 x : 0≤F x := mul_nonneg (hD0 x) (W.nonneg _)
  have fD x : F x≤D x :=
    (mul_le_mul_of_nonneg_left (W.le_one _) (hD0 x)).trans_eq (mul_one _)
  have bF : BMeas F := bD.mul (BMeas.of_unit (rowMeasurable W v)
    (fun _=>W.nonneg _) (fun _=>W.le_one _))
  let e : X→ℝ := fun x=>t*F x
  have be : BMeas e := bF.scale t
  have e0 x : 0≤e x := mul_nonneg ht0 (f0 x)
  have eD x : e x≤D x := ((mul_le_mul_of_nonneg_right ht1 (f0 x)).trans_eq (one_mul _)).trans (fD x)
  have hE : (∫ x,e x ∂μ)=1/2-b := by
    change (∫ x,t*F x ∂μ)=_
    rw [integral_const_mul,hm,ht]
  have hEE : energyPair μ W e e=0 := by
    unfold e
    rw [energy_scale_left,energy_scale_right]
    change t*(t*energyPair μ W F F)=0
    rw [hN]
    ring
  have hAE : energyPair μ W a e≤(b/2)*(1/2-b) := by
    rw [energy_row μ W a e ba be]
    simp only [weightedDegree_eq_reweight μ W a ha ha0]
    rw [← hE,← integral_const_mul]
    apply integral_mono (bMeas_integrable μ (be.mul (deg_bmeas _ W)))
      ((bMeas_integrable μ be).const_mul (b/2))
    intro x
    change e x*deg (reweight μ a) W x ≤ (b/2)*e x
    by_cases he : e x=0
    · simp [he]
    · have hp : 0<D x := (lt_of_le_of_ne (e0 x) (Ne.symm he)).trans_le (eD x)
      rw [mul_comm (b/2)]
      exact mul_le_mul_of_nonneg_left (hdeg x hp) (e0 x)
  let H : Half μ := ⟨a+e,(ba.add be).1,fun x=>add_nonneg (ha0 x) (e0 x),
    fun x=>by change a x+e x≤1; linarith [eD x,hcap x],by
      rw [integral_add' (bMeas_integrable μ ba) (bMeas_integrable μ be),hA,hE]; ring⟩
  have h := csInf_le (range_bdd μ W) (show halfEnergy μ W H∈range (halfEnergy μ W) from ⟨H,rfl⟩)
  rw [halfEnergy_as_pair] at h
  change beta μ W≤energyPair μ W (a+e) (a+e)/2 at h
  rw [energy_add_left μ W a e (a+e) ba be (ba.add be),energy_add_right μ W a a e ba ba be,
    energy_add_right μ W e a e be ba be,energy_symm μ W e a,hEE] at h
  unfold greedyCaseOne
  linarith

#print axioms greedy_kernel_case_one
end SparseHalfGraphon
