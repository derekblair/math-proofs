import GeometricPairMoment

namespace RobustFolkman.GeometricGap
open MeasureTheory Set Finset WithLp
open scoped ENNReal InnerProductSpace
variable {J E : Type*} [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E]

theorem lostRootTriangle_measurable (t w : ℝ) (a : UnitSphere E) :
    MeasurableSet (lostRootTriangle t w a) := by
  let U : Set ThreeReals := {p | w≤p.1 ∨ w≤p.2.1}
  rw [←fixedRootExcess_lost]
  exact (fixedRootExcess_continuous t a).measurable
    ((triangleExcessRegion_measurable t).inter
      ((measurableSet_le measurable_const measurable_fst).union
        (measurableSet_le measurable_const (measurable_fst.comp measurable_snd))))

theorem fixed_root_lost_count_markov (m : ℕ) (dim : Module.finrank ℝ E=3+m+1)
    (t A : ℝ) (t0 : 0<t) (t1 : t≤1/8) (large : 36≤(m:ℝ)/2) (dense : 1≤((m:ℝ)/2)*t^2)
    (a : UnitSphere E) (κ : ℝ≥0∞) (κ0 : κ≠0) (κtop : κ≠∞)
    (j0 : ((offDiagonal : Finset (J×J)).card:ℝ≥0∞)≠0)
    (p0 : ((uniformSphere (volume : Measure E)).prod (uniformSphere (volume : Measure E)))
      (triangleAt t a) ≠ 0) :
    let σ := uniformSphere (volume : Measure E)
    let w := A/(((m:ℝ)/2)*t)
    let e := ((offDiagonal : Finset (J×J)).card:ℝ≥0∞)*(σ.prod σ) (triangleAt t a)
    (Measure.pi fun _ : J => σ)
       {x | κ*e≤samplePairCount (J:=J) (lostRootTriangle t w a) x} ≤
       2*ENNReal.ofReal (Real.exp (36-A))/κ := by
  intro σ w e
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  have e0 : e≠0 := mul_ne_zero j0 p0
  have et : e≠∞ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (measure_ne_top (σ.prod σ) _)
  have k0 : κ*e≠0 := mul_ne_zero κ0 e0
  have kt : κ*e≠∞ := ENNReal.mul_ne_top κtop et
  have tail := samplePairCount_markov (J:=J) σ (lostRootTriangle t w a)
    (lostRootTriangle_measurable t w a) (κ*e) k0 kt
  have loss := fixed_root_shell_loss (E:=E) m dim t A t0 t1 large dense a
  refine tail.trans ?_
  calc
    _ ≤ (((offDiagonal : Finset (J×J)).card:ℝ≥0∞)*
       ((2*ENNReal.ofReal (Real.exp (36-A)))*(σ.prod σ) (triangleAt t a)))/(κ*e) := by gcongr
    _ = ((2*ENNReal.ofReal (Real.exp (36-A)))*e)/(κ*e) := by congr 1; dsimp [e]; ac_rfl
    _ = _ := ENNReal.mul_div_mul_right _ _ e0 et

#print axioms fixed_root_lost_count_markov
end RobustFolkman.GeometricGap
