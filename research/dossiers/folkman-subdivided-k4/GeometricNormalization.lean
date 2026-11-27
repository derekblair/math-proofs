import GeometricChartVolume

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory Set
open scoped ENNReal
variable {I : Type*} [Fintype I] [LinearOrder I]

/-- In the unconditioned correlation chart the maximum determinant is 1.
The threshold parameter is immaterial when the constraint relation is empty. -/
theorem chart_unrestricted_max (n : Fintype.card I≤6) :
    GramFeasible (fun _ _ : I => False) (1/40000) (1 : Matrix I I ℝ) ∧
    ∀ A : Matrix I I ℝ, GramFeasible (fun _ _ : I => False) (1/40000) A → A.det≤1 := by
  let C : I→I→Prop := fun _ _ => False
  have sym (i j : I) : C i j ↔ C j i := Iff.rfl
  obtain ⟨M,mf,max⟩ := gram_max_exists C sym n (1/40000) (by norm_num) (by norm_num)
  have free_iff (A : Matrix I I ℝ) (u v : ℝ) : GramFeasible C u A ↔ GramFeasible C v A := by
    simp [GramFeasible,C]
  have eq : M=1 := by
    ext i j
    by_cases ij : i=j
    · subst j
      simpa using mf.2.1 i
    · rw [Matrix.one_apply_ne ij]
      by_contra nz
      let u := min (1/40000 : ℝ) |M i j|
      have u0 : 0<u := lt_min (by norm_num) (abs_pos.mpr nz)
      have uf : u≤1/20000 := (min_le_left _ _).trans (by norm_num)
      have su := (all_pairs_saturation C sym n u u0 uf M ((free_iff M _ _).mp mf)
        (fun A hA => max A ((free_iff A _ _).mpr hA)) i j ij).2 (by exact id)
      have le : u≤|M i j| := min_le_right _ _
      linarith
  subst M
  exact ⟨mf,fun A hA => by simpa using max A hA⟩

/-- No gamma-function computation is needed for the exponential rate of
the normalizer: the unconditioned Gram region has determinant maximum 1,
and a positive-volume superlevel at every level below 1. -/
theorem chart_normalizer_sandwich (n : Fintype.card I≤6) (k : ℝ) (hk : k<1) :
    ∃ c : ℝ≥0∞, 0<c ∧ c<∞ ∧ ∀ p : ℝ, 0≤p →
      (ENNReal.ofReal k)^p*c ≤
        (∫⁻ x in chartRegion (fun _ _ : I => False) (1/40000),
          (ENNReal.ofReal (gramChart x).det)^p) ∧
      (∫⁻ x in chartRegion (fun _ _ : I => False) (1/40000),
          (ENNReal.ofReal (gramChart x).det)^p) ≤
        volume (chartRegion (fun _ _ : I => False) (1/40000)) := by
  obtain ⟨feas,opt⟩ := chart_unrestricted_max n
  simpa using chart_determinant_sandwich (fun _ _ : I => False) (fun _ _ => Iff.rfl)
    n (1/40000) (by norm_num) le_rfl (1 : Matrix I I ℝ) feas
    (fun A hA => by simpa using opt A hA) k (by simpa using hk)

#print axioms chart_normalizer_sandwich
end RobustFolkman.GeometricGap
