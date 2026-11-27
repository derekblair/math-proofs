import GeometricBandResidualLaw
import GeometricCapCount

namespace RobustFolkman.GeometricGap
open MeasureTheory Set WithLp Finset
open scoped ENNReal BigOperators
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]

/-- A uniform failure probability in all sufficiently large retained
samples is also a failure probability under the original height law. -/
theorem band_bad_mixture (m : ℕ) (dim : Module.finrank ℝ W=m+2)
    (H : Set (I→ℝ)) (Hm : MeasurableSet H)
    (P : Finset J → Prop) [DecidablePred P]
    (B : (L : Finset J) → Set ({i : J // i∈L}→UnitSphere W))
    (Bm : ∀ L, MeasurableSet (B L)) (ε : ℝ≥0∞) :
    let σ := uniformSphere (volume : Measure (SphereAmbient I W))
    let A := sphereCoord ⁻¹' H
    let μ := Measure.pi (fun _ : J => σ)
    let τ := uniformSphere (volume : Measure W)
    σ A≠0 → σ Aᶜ≠0 →
    (∀ L, P L → (Measure.pi (fun _ : {i : J // i∈L} => τ)) (B L)≤ε) →
    μ (⋃ L ∈ (Finset.univ.filter P : Finset (Finset J)),
      {(x : J→UnitSphere (SphereAmbient I W)) | retained A x=L ∧
        (fun i : {i : J // i∈L} => sphereResidual (x i.val))∈B L}) ≤ ε := by
  classical
  intro σ A μ τ a0 a1 hb
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let U : Finset (Finset J) := Finset.univ.filter P
  let F := fun L : Finset J => Set.univ.pi (labelSlices A L)
  let G := fun L : Finset J =>
    (fun (x : J→UnitSphere (SphereAmbient I W)) (i : {i : J // i∈L}) => sphereResidual (x i.val)) ⁻¹' B L
  have Am : MeasurableSet A := sphereCoord_measurable Hm
  have Fm (L : Finset J) : MeasurableSet (F L) := by
    apply MeasurableSet.pi Set.countable_univ
    intro i _
    by_cases h : i∈L <;> simp [labelSlices,h,Am,Am.compl]
  have Gm (L : Finset J) : MeasurableSet (G L) := by
    apply (Measurable.of_eval (fun (i : {j : J // j∈L}) => sphereResidual_measurable.comp (measurable_pi_apply i.val)))
    exact Bm L
  have eq : (⋃ L ∈ U, {(x : J→UnitSphere (SphereAmbient I W)) | retained A x=L ∧
      (fun i : {i : J // i∈L} => sphereResidual (x i.val))∈B L}) =
      ⋃ L ∈ U, G L∩F L := by
    ext x
    simp [G,F,(retained_iff A),and_comm]
  have disj : (↑U : Set (Finset J)).PairwiseDisjoint F := by
    intro L _ R _ ne
    apply Set.disjoint_left.2
    intro x hL hR
    exact ne (((retained_iff A L x).2 hL).symm.trans ((retained_iff A R x).2 hR))
  have fsum : (∑ L ∈ U, μ (F L))≤1 := by
    rw [←measure_biUnion_finset disj (fun L _ => Fm L)]
    exact prob_le_one
  change μ (⋃ L ∈ U, _)≤_
  rw [eq]
  calc
    _ ≤ ∑ L ∈ U, μ (G L∩F L) := measure_biUnion_finset_le U _
    _ ≤ ∑ L ∈ U, μ (F L)*ε := by
      apply Finset.sum_le_sum
      intro L hL
      have h := band_residual_selected_event (I:=I) (J:=J) (W:=W) m dim H Hm L (B L) (Bm L) a0 a1
      change μ.restrict (F L) (G L)=_ at h
      rw [Measure.restrict_apply (Gm L)] at h
      have law : μ (F L)=(σ A)^L.card*(σ Aᶜ)^(Fintype.card J-L.card) := by
        unfold F μ
        rw [Measure.pi_pi,keepLabels_mass_formula]
      rw [h,law]
      gcongr
      exact hb L (Finset.mem_filter.1 hL).2
    _ = (∑ L ∈ U, μ (F L))*ε := by rw [Finset.sum_mul]
    _ ≤ _ := by simpa only [one_mul] using mul_le_mul_left fsum ε

#print axioms band_bad_mixture
end RobustFolkman.GeometricGap
