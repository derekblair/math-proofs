import GeometricQuadraticCuts

namespace RobustFolkman.GeometricGap
open Matrix Finset
variable {V : Type*} [DecidableEq V] [Fintype V]

noncomputable def rowDegree (W : Matrix V V ℝ) (i : V) := ∑ j, W i j

noncomputable def normAdj (W : Matrix V V ℝ) : Matrix V V ℝ :=
  fun i j => (Real.sqrt (rowDegree W i))⁻¹ * W i j * (Real.sqrt (rowDegree W j))⁻¹

theorem normalized_quad_on_cut (W : Matrix V V ℝ) (sys : W.IsSymm)
    (pos : ∀ i j, 0≤W i j) (b : V→Bool) :
    let z := fun i => Real.sqrt (rowDegree W i)*cutSign b i
    z ⬝ᵥ (normAdj W *ᵥ z)=cutSign b ⬝ᵥ (W*ᵥcutSign b) := by
  intro z
  have nn (i : V) : 0≤rowDegree W i := Finset.sum_nonneg fun j _ => pos i j
  have entry (i j : V) : W i j≤rowDegree W i :=
    Finset.single_le_sum (fun k _ => pos i k) (Finset.mem_univ j)
  have sym (i j : V) : W i j=W j i := by
    simpa [Matrix.transpose_apply] using congrFun (congrFun sys.eq j) i
  have point (i j : V) : z i*(normAdj W i j*z j)=cutSign b i*(W i j*cutSign b j) := by
    by_cases hi : rowDegree W i=0
    · have W0 : W i j=0 := le_antisymm ((entry i j).trans_eq hi) (pos i j)
      simp [normAdj,W0]
    by_cases hj : rowDegree W j=0
    · have W0 : W i j=0 := by
        rw [sym i j]
        exact le_antisymm ((entry j i).trans_eq hj) (pos j i)
      simp [normAdj,W0]
    dsimp [z,normAdj]
    have si : Real.sqrt (rowDegree W i)≠0 := (Real.sqrt_pos.2 (lt_of_le_of_ne (nn i) (Ne.symm hi))).ne'
    have sj : Real.sqrt (rowDegree W j)≠0 := (Real.sqrt_pos.2 (lt_of_le_of_ne (nn j) (Ne.symm hj))).ne'
    field_simp
    <;> ring
  change (∑ i, z i*(∑ j, normAdj W i j*z j)) = ∑ i, cutSign b i*(∑ j, W i j*cutSign b j)
  simp_rw [Finset.mul_sum,point]

theorem normalized_cut_square (W : Matrix V V ℝ) (pos : ∀ i j, 0≤W i j) (b : V→Bool) :
    (∑ i, (Real.sqrt (rowDegree W i)*cutSign b i)^2) = ∑ i, ∑ j, W i j := by
  apply Finset.sum_congr rfl
  intro i _
  have h : 0≤rowDegree W i := Finset.sum_nonneg fun j _ => pos i j
  rw [mul_pow,Real.sq_sqrt h]
  cases bi : b i <;> norm_num [cutSign,bi,rowDegree]

theorem weighted_cut_from_normalized_lower_spectrum (W : Matrix V V ℝ) (sys : W.IsSymm)
    (pos : ∀ i j, 0≤W i j) (b : V→Bool) (ρ : ℝ)
    (spec : ∀ x : V→ℝ, -ρ*(∑ i, (x i)^2) ≤ x ⬝ᵥ (normAdj W *ᵥ x)) :
    (∑ i, ∑ j, W i j*edgeFlip b i j)≤((1+ρ)/2)*(∑ i, ∑ j, W i j) := by
  apply weighted_cut_bound
  have h := spec (fun i => Real.sqrt (rowDegree W i)*cutSign b i)
  rwa [normalized_quad_on_cut W sys pos b,normalized_cut_square W pos b] at h

#print axioms weighted_cut_from_normalized_lower_spectrum
end RobustFolkman.GeometricGap
