import GeometricGramConditional

namespace RobustFolkman.GeometricGap
open MeasureTheory Set Matrix
open scoped ENNReal InnerProductSpace
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- Exact conditional one-point anchor law, with no chosen basis in its
statement. The right-hand side depends only on the old anchor Gram
matrix. The orthonormal basis may be chosen separately for each tuple. -/
theorem sphere_fixed_anchor_conditional (v : I→E) (vi : LinearIndependent ℝ v)
    (m : ℕ) (dim : Module.finrank ℝ E=Fintype.card I+m+2)
    (g : (I→ℝ)→ℝ≥0∞) (gm : Measurable g) :
    let A := anchorGram v
    (∫⁻ x : UnitSphere E, g (fun i => ⟪v i,x.val⟫_ℝ) ∂uniformSphere (volume : Measure E)) =
      (∫⁻ y in {y | anchorQuad A y<1},
        ENNReal.ofReal ((Real.sqrt A.det)⁻¹) *
          (g y*ENNReal.ofReal ((Real.sqrt (1-anchorQuad A y))^m))) /
        (∫⁻ u in (projectionBall : Set (I→ℝ)), projectionFactor m u) := by
  let K := Submodule.span ℝ (Set.range v)
  let q : I→K := fun i => ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩
  have qind : LinearIndependent ℝ q := LinearIndependent.of_comp K.subtype vi
  have kd : Module.finrank ℝ K = Fintype.card I := finrank_span_eq_card vi
  have rd : Module.finrank ℝ Kᗮ = m+2 := by
    have h := K.finrank_add_finrank_orthogonal
    omega
  let b : OrthonormalBasis I ℝ K :=
    (stdOrthonormalBasis ℝ K).reindex (Fintype.equivFinOfCardEq kd.symm).symm
  exact sphere_anchor_conditional K b q qind m rd g gm

#print axioms sphere_fixed_anchor_conditional
end RobustFolkman.GeometricGap
