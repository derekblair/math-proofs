import GeometricChartBorder

namespace RobustFolkman.GeometricGap
open MeasureTheory Matrix Set
open scoped ENNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def sampleChart {k : ℕ} (u : Fin k→UnitSphere E) : PairCoord (Fin k)→ℝ :=
  fun p => ⟪(u p.val.1).val,(u p.val.2).val⟫_ℝ

theorem sampleChart_measurable [SecondCountableTopology E] {k : ℕ} : Measurable (sampleChart (E:=E) (k:=k)) := by
  apply Measurable.of_eval
  intro p
  exact ((continuous_subtype_val.comp (continuous_apply p.val.1)).inner
    (continuous_subtype_val.comp (continuous_apply p.val.2))).measurable

theorem sampleChart_matrix {k : ℕ} (u : Fin k→UnitSphere E) :
    gramChart (sampleChart u)=anchorGram (fun i => (u i).val) := by
  have herm : (anchorGram (fun i => (u i).val)).IsHermitian := by
    ext i j
    exact real_inner_comm _ _
  have diag (i : Fin k) : anchorGram (fun j => (u j).val) i i=1 := by
    unfold anchorGram
    have norm : ‖(u i).val‖=1 := by simpa [Metric.mem_sphere,dist_zero_right] using (u i).property
    rw [real_inner_self_eq_norm_sq,norm,one_pow]
  exact gramChart_surjective_on_correlation _ herm diag

theorem sampleChart_snoc {k : ℕ} (v : Fin k→UnitSphere E) (x : UnitSphere E) :
    chartStep k (sampleChart (Fin.snoc (α:=fun _ => UnitSphere E) v x)) =
      (sampleChart v, fun i => ⟪(v i).val,x.val⟫_ℝ) := by
  rw [chartStep_coords]
  congr 1
  · funext p
    simp [sampleChart,pairStepMap]
  · funext i
    simp [sampleChart,pairStepMap]

#print axioms sampleChart_snoc
end RobustFolkman.GeometricGap
