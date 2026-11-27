import GeometricSampleChart
import GeometricNormalization

namespace RobustFolkman.GeometricGap
open MeasureTheory Matrix Set
open scoped ENNReal

def chartPD (k : ℕ) : Set (PairCoord (Fin k)→ℝ) := {x | (gramChart x).PosDef}

noncomputable def chartWeight (k m : ℕ) (x : PairCoord (Fin k)→ℝ) : ℝ≥0∞ :=
  (chartPD k).indicator (fun x => ENNReal.ofReal ((Real.sqrt (gramChart x).det)^m)) x

theorem chartPD_measurable (k : ℕ) : MeasurableSet (chartPD k) := by
  let S := chartRegion (I:=Fin k) (fun _ _ => False) 0
  have eq : chartPD k = S ∩ {x | (gramChart x).det≠0} := by
    ext x
    change (gramChart x).PosDef ↔ GramFeasible (fun _ _ => False) 0 (gramChart x) ∧ (gramChart x).det≠0
    simp only [GramFeasible,gramChart_diag,false_implies,implies_true,and_true]
    constructor
    · exact fun h => ⟨h.posSemidef,h.det_pos.ne'⟩
    · exact fun h => pd_of_psd_det _ h.1 h.2
  rw [eq]
  exact (chartRegion_compact (I:=Fin k) _ _).measurableSet.inter
    (isOpen_ne.preimage (gram_det_continuous.comp gramChart_continuous)).measurableSet

theorem chartWeight_measurable (k m : ℕ) : Measurable (chartWeight k m) := by
  exact (((gram_det_continuous.comp gramChart_continuous).measurable.sqrt).pow_const _).ennreal_ofReal.indicator
    (chartPD_measurable k)

theorem chartWeight_at_pd (k m : ℕ) (x : PairCoord (Fin k)→ℝ)
    (pd : (gramChart x).PosDef) :
    chartWeight k m x = ENNReal.ofReal ((Real.sqrt (gramChart x).det)^m) :=
  indicator_of_mem (s:=chartPD k) (a:=x) pd _

theorem chartWeight_positive (k m : ℕ) (x : PairCoord (Fin k)→ℝ)
    (pd : (gramChart x).PosDef) : 0<chartWeight k m x := by
  rw [chartWeight_at_pd k m x pd]
  exact ENNReal.ofReal_pos.mpr (pow_pos (Real.sqrt_pos.2 pd.det_pos) _)

theorem chartWeight_finite (k m : ℕ) (x : PairCoord (Fin k)→ℝ) :
    chartWeight k m x ≠ ∞ := by
  unfold chartWeight
  by_cases h : x∈chartPD k
  · rw [indicator_of_mem h]
    exact ENNReal.ofReal_ne_top
  · simp [indicator_of_notMem h]

theorem chartWeight_split (k m : ℕ) (u : PairCoord (Fin k)→ℝ) (y : Fin k→ℝ)
    (pd : (gramChart u).PosDef) :
    chartWeight (k+1) m ((chartStep k).symm (u,y)) =
    (if anchorQuad (gramChart u) y<1 then
      chartWeight k (m+1) u *
        (ENNReal.ofReal ((Real.sqrt (gramChart u).det)⁻¹) *
          ENNReal.ofReal ((Real.sqrt (1-anchorQuad (gramChart u) y))^m))
      else 0) := by
  let x := (chartStep k).symm (u,y)
  have e : chartStep k x=(u,y) := (chartStep k).apply_symm_apply _
  have p : (gramChart x).PosDef ↔ anchorQuad (gramChart u) y<1 := by
    rw [gramChart_border_pd k x,e]
    exact gram_border_pd _ pd _
  by_cases h : anchorQuad (gramChart u) y<1
  · rw [if_pos h,chartWeight_at_pd _ _ _ (p.mpr h),chartWeight_at_pd _ _ _ pd,
      gramChart_border_det k x,e,gram_border_det _ (isUnit_iff_ne_zero.mpr pd.det_pos.ne') y]
    have s0 := Real.sqrt_pos.2 pd.det_pos
    rw [Real.sqrt_mul pd.det_pos.le, mul_pow,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr s0.le),
      ← ENNReal.ofReal_mul (pow_nonneg s0.le _)]
    congr 1
    rw [pow_succ]
    field_simp
  · rw [if_neg h]
    unfold chartWeight
    apply indicator_of_notMem
    exact h ∘ p.mp

#print axioms chartWeight_split
end RobustFolkman.GeometricGap
