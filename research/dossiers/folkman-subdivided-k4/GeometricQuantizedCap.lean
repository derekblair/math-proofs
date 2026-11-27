import GeometricGridOperator
import GeometricPairStrip

namespace RobustFolkman.GeometricGap
open MeasureTheory Set Matrix WithLp
open scoped InnerProductSpace ENNReal BigOperators Matrix.Norms.L2Operator

noncomputable def quantizedCapKernel {d m : ℕ} [Nontrivial (EuclideanSpace ℝ (Fin d))]
    (t : ℝ) (a : GridSphere d) (i j : GridCode d m) : ℝ :=
  capKernel t (cellRepresentative a i) (cellRepresentative a j)

theorem quantized_cap_strip {d m : ℕ} [Nontrivial (EuclideanSpace ℝ (Fin d))]
    (mp : 0<m) (t : ℝ) (a : GridSphere d) (z : GridSphere d×GridSphere d) :
    let δ := 2*(Real.sqrt (d:ℝ)/(m:ℝ))
    ‖quantizedCapKernel t a (gridCode d m z.1) (gridCode d m z.2)-capKernel t z.1 z.2‖ ≤
      (pairHeightStrip (t-δ) (t+δ)).indicator (fun _ => 1) z := by
  intro δ
  let R := cellRepresentative a ∘ gridCode d m
  have er : |⟪(R z.1).val,(R z.2).val⟫_ℝ-⟪z.1.val,z.2.val⟫_ℝ|≤δ :=
    grid_inner_error mp a z.1 z.2
  have calcK (x y : GridSphere d) : capKernel t x y =
    if t≤⟪x.val,y.val⟫_ℝ then 1 else 0 := by
    unfold capKernel
    rfl
  have kg : quantizedCapKernel t a (gridCode d m z.1) (gridCode d m z.2)
    = capKernel t (R z.1) (R z.2) := rfl
  rw [kg,calcK,calcK]
  by_cases h : t≤⟪z.1.val,z.2.val⟫_ℝ <;> by_cases k : t≤⟪(R z.1).val,(R z.2).val⟫_ℝ
  · simp only [ite_eq_left h,ite_eq_left k,sub_self,norm_zero]
    exact indicator_nonneg (fun _ _ => zero_le_one) _
  · have s : z∈pairHeightStrip (t-δ) (t+δ) := threshold_disagreement_in_strip _ _ _ _ er
      (fun hiff => k (hiff.1 h))
    norm_num [h,k,indicator_of_mem s]
  · have s : z∈pairHeightStrip (t-δ) (t+δ) := threshold_disagreement_in_strip _ _ _ _ er
      (fun hiff => h (hiff.2 k))
    norm_num [h,k,indicator_of_mem s]
  · simp only [ite_eq_right h,ite_eq_right k,sub_self,norm_zero]
    exact indicator_nonneg (fun _ _ => zero_le_one) _

/-- The sphere's exact geometric grid has a centered covariance operator
bounded by the population gap plus an explicit strip contribution. -/
theorem quantized_centered_cap_operator (n m : ℕ)
    [Nontrivial (EuclideanSpace ℝ (Fin (n+3)))]
    (mp : 0<m) (t : ℝ) (tp : 0<t) (ts : t≤1/8) (large : 3≤(n:ℝ)/2)
    (dense : 1≤4*((n:ℝ)/2)*t^2) (a : GridSphere (n+3))
    (low : -1≤t-2*(Real.sqrt ((n+3:ℕ):ℝ)/(m:ℝ)))
    (high : t+2*(Real.sqrt ((n+3:ℕ):ℝ)/(m:ℝ))≤1) :
    let d := n+3
    let δ := 2*(Real.sqrt (d:ℝ)/(m:ℝ))
    let σ := uniformSphere (volume : Measure (EuclideanSpace ℝ (Fin d)))
    let Z := (sliceMass ((n:ℝ)/2) (-1) 1).toReal
    let q := σ.real (capPoints t a)
    let p := fun i => σ.real (gridCode d m ⁻¹' {i})
    let A : Matrix (GridCode d m) (GridCode d m) ℝ :=
      fun i j => Real.sqrt (p i)*Real.sqrt (p j)*(quantizedCapKernel t a i j-q)
    ‖A‖ ≤ q*Real.sqrt (squaredCapContraction n t)+Real.sqrt (2*δ/Z) := by
  classical
  intro d δ σ Z q p A
  have dim : Module.finrank ℝ (EuclideanSpace ℝ (Fin d))=n+3 := by simp [d]
  have mc (i : GridCode d m) : MeasurableSet (gridCode d m ⁻¹' {i}) :=
    gridCode_measurable d m (measurableSet_singleton i)
  have δ0 : 0≤δ := by dsimp [δ]; positivity
  have sym : A.IsHermitian := by
    ext i j
    simp only [conjTranspose_apply,star_trivial]
    change Real.sqrt (p j)*Real.sqrt (p i)*(capKernel t (cellRepresentative a j) (cellRepresentative a i)-q)
      = Real.sqrt (p i)*Real.sqrt (p j)*(capKernel t (cellRepresentative a i) (cellRepresentative a j)-q)
    rw [capKernel_symm t (cellRepresentative a j),mul_comm (Real.sqrt (p j)) (Real.sqrt (p i))]
  have strip := pair_strip_real_bound n dim (t-δ) (t+δ) low high (by linarith only [δ0])
  change (σ.prod σ).real (pairHeightStrip (t-δ) (t+δ)) ≤ (t+δ-(t-δ))/Z at strip
  rw [show t+δ-(t-δ)=2*δ by ring] at strip
  refine real_symmetric_matrix_norm_bound A sym _ (by
    exact add_nonneg (mul_nonneg ENNReal.toReal_nonneg (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) ?_
  intro v
  have h := grid_centered_cap_quadratic n dim t tp ts large dense a
    (gridCode d m) mc (quantizedCapKernel t a) _ (pairHeightStrip_measurable _ _)
    (quantized_cap_strip mp t a) v
  change ‖∑ i, ∑ j, A i j*(v i*v j)‖ ≤ _ at h
  exact h.trans (mul_le_mul_of_nonneg_right (add_le_add_right (Real.sqrt_le_sqrt strip) _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))

#print axioms quantized_centered_cap_operator
end RobustFolkman.GeometricGap
