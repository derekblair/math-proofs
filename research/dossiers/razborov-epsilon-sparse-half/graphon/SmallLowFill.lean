import AllocationLoads

open Set MeasureTheory Function Filter
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- An almost-half independent outside set needs only a small residual
fill. No integrality or atomless trimming assumption is used. -/
theorem small_low_independent_fill (W : Kernel X) (I L : Set X) (hI : MeasurableSet I)
    (hL : MeasurableSet L) (hd : Disjoint I L)
    (hℓ : μ.real L<1/10) (hsize : 1/2-(μ.real L)/2<μ.real I)
    (hInd : ∀ᵐ z ∂μ.prod μ, z.1∈I → z.2∈I → W.W z=0)
    (hcross : ∀ x∈L, deg (μ.restrict I) W x≤3/10) :
    beta μ W<1/50 := by
  have hI0 : 0≤μ.real I := measureReal_nonneg
  let q : ℝ := min (1/2) (μ.real I)
  let r : ℝ := 1/2-q
  have q0 : 0≤q := le_min (by norm_num) hI0
  have qI : q≤μ.real I := min_le_right _ _
  have r0 : 0≤r := sub_nonneg.mpr (min_le_left _ _)
  have rlt : r<1/20 := by
    dsimp [r,q]
    rcases le_total (1/2:ℝ) (μ.real I) with h | h
    · rw [min_eq_left h]
      norm_num
    · rw [min_eq_right h]
      linarith
  have rL : r≤μ.real L := by
    dsimp [r,q]
    rcases le_total (1/2:ℝ) (μ.real I) with h | h
    · rw [min_eq_left h,sub_self]
      exact measureReal_nonneg
    · rw [min_eq_right h]
      linarith [measureReal_nonneg (μ:=μ) (s:=L)]
  let d : X→ℝ := allocSet μ I q
  let e : X→ℝ := allocSet μ L r
  have bD : BMeas d := allocSet_bmeas μ I hI q q0 qI
  have bE : BMeas e := allocSet_bmeas μ L hL r r0 rL
  have d0 x : 0≤d x := allocSet_nn μ I q q0 x
  have e0 x : 0≤e x := allocSet_nn μ L r r0 x
  have dm : (∫ x,d x ∂μ)=q := allocSet_mass μ I hI q q0 qI
  have em : (∫ x,e x ∂μ)=r := allocSet_mass μ L hL r r0 rL
  have hDD : energyPair μ W d d=0 := by
    unfold energyPair
    have hzero : (fun z : X×X=>d z.1*d z.2*W.W z) =ᵐ[μ.prod μ] 0 := by
      classical
      filter_upwards [hInd] with z hz
      by_cases hs : z.1∈I
      · by_cases ht : z.2∈I
        · simp [hz hs ht]
        · simp [d,allocSet,ht]
      · simp [d,allocSet,hs]
    rw [integral_congr_ae hzero]
    exact integral_zero _ _
  have hEE : energyPair μ W e e≤r*r := by
    simpa only [em] using energy_cross_bound μ W e e bE bE e0 e0
  have hddeg (y : X) : weightedDegree μ W d y ≤ deg (μ.restrict I) W y := by
    classical
    unfold weightedDegree deg
    rw [← integral_indicator hI]
    have hi : Integrable (fun x=>d x*W.W (x,y)) μ := bMeas_integrable μ
      (bD.mul (BMeas.of_unit (W.measurable_W.comp (measurable_id.prodMk measurable_const))
        (fun _=>W.nonneg _) (fun _=>W.le_one _)))
    apply integral_mono hi ((row_integrable μ W y).indicator hI)
    intro x
    by_cases h : x∈I
    · rw [indicator_of_mem h, W.symm y x]
      exact (mul_le_mul_of_nonneg_right (allocSet_le μ I q qI x) (W.nonneg _)).trans_eq (one_mul _)
    · simp [d,allocSet,h]
  have hDE : energyPair μ W d e≤(3/10)*r := by
    rw [energy_row μ W d e bD bE,← em,← integral_const_mul]
    have bd := load_bmeas μ W bD
    have hdu : weightedDegree μ W d=load μ W d := by
      funext y
      unfold weightedDegree load
      apply integral_congr_ae
      exact ae_of_all _ (fun x=>by change d x*W.W (x,y)=d x*W.W (y,x); rw [W.symm x y])
    rw [hdu]
    apply integral_mono (bMeas_integrable μ (bE.mul bd)) ((bMeas_integrable μ bE).const_mul _)
    intro x
    classical
    change e x * load μ W d x ≤ (3/10)*e x
    by_cases h : x∈L
    · rw [← hdu,mul_comm (3/10) (e x)]
      exact mul_le_mul_of_nonneg_left ((hddeg x).trans (hcross x h)) (e0 x)
    · simp [e,allocSet,h]
  let H : Half μ := ⟨d+e,(bD.add bE).1,fun x=>add_nonneg (d0 x) (e0 x),by
    intro x
    classical
    by_cases hx : x∈I
    · have hy : x∉L := fun h=>Set.disjoint_left.mp hd hx h
      change d x+e x≤1
      rw [show e x=0 from allocSet_support μ L r hy,add_zero]
      exact allocSet_le μ I q qI x
    · change d x+e x≤1
      rw [show d x=0 from allocSet_support μ I q hx,zero_add]
      exact allocSet_le μ L r rL x,
    by rw [integral_add' (bMeas_integrable μ bD) (bMeas_integrable μ bE),dm,em]; dsimp [r]; ring⟩
  have hcost : halfEnergy μ W H ≤ (3/10)*r+r*r/2 := by
    rw [halfEnergy_as_pair]
    change energyPair μ W (d+e) (d+e)/2≤_
    rw [energy_add_left μ W d e (d+e) bD bE (bD.add bE),
      energy_add_right μ W d d e bD bD bE,energy_add_right μ W e d e bE bD bE,
      hDD,energy_symm μ W e d]
    linarith
  have hstrict : (3/10)*r+r*r/2<1/50 := by
    nlinarith [mul_nonneg r0 (sub_nonneg.mpr rlt.le)]
  exact (csInf_le (range_bdd μ W) ⟨H,rfl⟩).trans_lt (hcost.trans_lt hstrict)

#print axioms small_low_independent_fill
end SparseHalfGraphon
