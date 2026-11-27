import GeometricQuantizedCap

namespace RobustFolkman.GeometricGap
open MeasureTheory Set Matrix WithLp
open scoped InnerProductSpace ENNReal BigOperators

theorem capKernel_eq_ite {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    (t : ℝ) (a b : UnitSphere E) :
    capKernel t a b = if t≤⟪a.val,b.val⟫_ℝ then 1 else 0 := by
  unfold capKernel
  rfl

theorem quantized_row_upper (n m : ℕ)
    [Nontrivial (EuclideanSpace ℝ (Fin (n+3)))]
    (mp : 0<m) (t : ℝ) (a : GridSphere (n+3)) (i : GridCode (n+3) m)
    (low : -1≤t-2*(Real.sqrt ((n+3:ℕ):ℝ)/(m:ℝ)))
    (high : t+2*(Real.sqrt ((n+3:ℕ):ℝ)/(m:ℝ))≤1) :
    let d := n+3
    let δ := 2*(Real.sqrt (d:ℝ)/(m:ℝ))
    let σ := uniformSphere (volume : Measure (EuclideanSpace ℝ (Fin d)))
    let Z := (sliceMass ((n:ℝ)/2) (-1) 1).toReal
    let q := σ.real (capPoints t a)
    let p := fun j => σ.real (gridCode d m ⁻¹' {j})
    ∑ j, p j*quantizedCapKernel t a i j ≤ q+2*δ/Z := by
  classical
  intro d δ σ Z q p
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let r := cellRepresentative a i
  let C := capPoints t r
  let L := rootHeightStrip r (t-δ) (t+δ)
  let c := fun j : GridCode d m => quantizedCapKernel t a i j
  let b := fun x : GridSphere d => c (gridCode d m x)
  have Cm : MeasurableSet C := capPoints_measurable t r
  have Lm : MeasurableSet L := rootHeightStrip_measurable r _ _
  have mc (j : GridCode d m) : MeasurableSet (gridCode d m ⁻¹' {j}) :=
    gridCode_measurable d m (measurableSet_singleton j)
  have d0 : 0≤δ := by dsimp [δ]; positivity
  have b_le (x : GridSphere d) : b x ≤ C.indicator (fun _ => 1) x + L.indicator (fun _ => 1) x := by
    change capKernel t r (cellRepresentative a (gridCode d m x))≤_
    rw [capKernel_eq_ite]
    by_cases h : t≤⟪r.val,(cellRepresentative a (gridCode d m x)).val⟫_ℝ
    · rw [ite_eq_left h]
      by_cases hm : x∈C
      · rw [indicator_of_mem hm]
        exact le_add_of_nonneg_right (indicator_nonneg (fun _ _ => zero_le_one) _)
      · have diff : |⟪r.val,(cellRepresentative a (gridCode d m x)).val⟫_ℝ-⟪r.val,x.val⟫_ℝ|≤δ := by
          rw [←inner_sub_right]
          have j := abs_real_inner_le_norm r.val ((cellRepresentative a (gridCode d m x)).val-x.val)
          have u : ‖r.val‖=1 := by simpa using r.property
          rw [u,one_mul] at j
          have k := gridRepresentative_dist mp a x
          have h0 : 0≤Real.sqrt (d:ℝ)/(m:ℝ) := by positivity
          apply (j.trans k).trans
          change Real.sqrt (d:ℝ)/(m:ℝ) ≤ 2*(Real.sqrt (d:ℝ)/(m:ℝ))
          linarith only [h0]
        have sub : x∈L := threshold_disagreement_in_strip _ _ _ _ diff
          (fun iff => hm (iff.2 h))
        rw [indicator_of_notMem hm,indicator_of_mem sub,zero_add]
    · rw [ite_eq_right h]
      exact add_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
        (indicator_nonneg (fun _ _ => zero_le_one) _)
  have CI : Integrable (C.indicator (fun _ => (1:ℝ))) σ := (integrable_const _).indicator Cm
  have LI : Integrable (L.indicator (fun _ => (1:ℝ))) σ := (integrable_const _).indicator Lm
  have ib := integral_mono (integrable_finite_code σ (gridCode d m) mc c) (CI.add LI) b_le
  change (∫ x,b x ∂σ) ≤ (∫ x, C.indicator (fun _ => 1) x + L.indicator (fun _ => 1) x ∂σ) at ib
  rw [integral_add CI LI,integral_indicator Cm,integral_indicator Lm] at ib
  simp only [integral_const,smul_eq_mul,mul_one,Measure.real,Measure.restrict_apply_univ] at ib
  have cm : (σ C).toReal=q := congrArg ENNReal.toReal (capPoints_mass_root_constant t r a)
  rw [cm] at ib
  have dim : Module.finrank ℝ (EuclideanSpace ℝ (Fin d))=n+3 := by simp [d]
  have ll := root_strip_real_bound n dim r (t-δ) (t+δ) low high (by linarith only [d0])
  change (σ L).toReal ≤ (t+δ-(t-δ))/Z at ll
  rw [show t+δ-(t-δ)=2*δ by ring] at ll
  have eq := integral_finite_code σ (gridCode d m) mc c
  exact eq.symm.le.trans (ib.trans (add_le_add_right ll _))

#print axioms quantized_row_upper
end RobustFolkman.GeometricGap
