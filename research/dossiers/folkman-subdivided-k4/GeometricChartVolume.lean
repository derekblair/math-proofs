import GeometricChart

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory Set
open scoped ENNReal
variable {I : Type*} [Fintype I] [LinearOrder I]

def chartRegion (C : I→I→Prop) (t : ℝ) : Set (PairCoord I→ℝ) :=
  {x | GramFeasible C t (gramChart x)}

theorem chartRegion_compact (C : I→I→Prop) (t : ℝ) :
    IsCompact (chartRegion C t) := by
  let cube : Set (PairCoord I→ℝ) := Set.pi Set.univ fun _ => Set.Icc (-1:ℝ) 1
  have cc : IsCompact cube := isCompact_univ_pi fun _ => isCompact_Icc
  apply cc.of_isClosed_subset ((closed_gram_feasible C t).preimage gramChart_continuous)
  intro x hx
  change GramFeasible C t (gramChart x) at hx
  intro i _
  have h := abs_entry_le_one _ hx.1 hx.2.1 i.val.1 i.val.2
  simpa [gramChart,i.property,mem_Icc] using (abs_le.mp h)

theorem chartRegion_volume_lt_top (C : I→I→Prop) (t : ℝ) :
    volume (chartRegion C t) < ∞ :=
  (chartRegion_compact C t).measure_lt_top

theorem chart_superlevel_volume_pos (C : I→I→Prop)
    (sym : ∀ i j, C i j ↔ C j i) (n : Fintype.card I≤6)
    (t : ℝ) (t0 : 0<t) (ts : t≤1/40000) (M : Matrix I I ℝ)
    (mf : GramFeasible C t M) (max : ∀ A, GramFeasible C t A → A.det≤M.det)
    (k : ℝ) (kk : k<M.det) :
    ∃ U : Set (PairCoord I→ℝ), IsOpen U ∧ 0<volume U ∧
      U⊆chartRegion C t ∧ ∀ x∈U, k<(gramChart x).det := by
  classical
  obtain ⟨pd,nm⟩ := optimum_is_localized C sym n t t0 (by linarith only [ts]) M mf max
  obtain ⟨Q,qp,qd,qe,hq,qc⟩ := strictly_feasible_approx C sym n t t0 ts M mf
    pd.det_pos nm (M.det-k) (sub_pos.mpr kk)
  obtain ⟨U,uo,un,uh⟩ := gram_open_inner C t k n Q qp.isHermitian qd qe
    (fun i j => (qc i j).trans_lt (by linarith only [ts])) (by linarith only [hq])
  exact ⟨U,uo,uo.measure_pos volume un,fun x hx => (uh x hx).1,fun x hx => (uh x hx).2⟩

theorem chart_determinant_sandwich (C : I→I→Prop)
    (sym : ∀ i j, C i j ↔ C j i) (n : Fintype.card I≤6)
    (t : ℝ) (t0 : 0<t) (ts : t≤1/40000) (M : Matrix I I ℝ)
    (mf : GramFeasible C t M) (max : ∀ A, GramFeasible C t A → A.det≤M.det)
    (k : ℝ) (kk : k<M.det) :
    ∃ c : ℝ≥0∞, 0<c ∧ c<∞ ∧ ∀ p : ℝ, 0≤p →
      (ENNReal.ofReal k)^p*c ≤
        (∫⁻ x in chartRegion C t, (ENNReal.ofReal (gramChart x).det)^p) ∧
      (∫⁻ x in chartRegion C t, (ENNReal.ofReal (gramChart x).det)^p) ≤
        (ENNReal.ofReal M.det)^p*volume (chartRegion C t) := by
  obtain ⟨U,uo,up,us,uk⟩ := chart_superlevel_volume_pos C sym n t t0 ts M mf max k kk
  refine ⟨volume U,up,(measure_mono us).trans_lt (chartRegion_volume_lt_top C t),fun p hp => ⟨?_,?_⟩⟩
  · exact RobustFolkman.lower_power_integral volume uo.measurableSet us _ _ p hp
      fun x hx => ENNReal.ofReal_le_ofReal (uk x hx).le
  · exact RobustFolkman.upper_power_integral volume (chartRegion_compact C t).measurableSet _ _ p hp
      fun x hx => ENNReal.ofReal_le_ofReal (max _ hx)

#print axioms chart_determinant_sandwich
end RobustFolkman.GeometricGap
