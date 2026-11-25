import Clip
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory Set
open scoped ENNReal

namespace PermCircles

instance realPlaneVolumeHaar : Measure.IsAddHaarMeasure volume (G := ℝ × ℝ) :=
  Measure.prod.instIsAddHaarMeasure _ _

def disk (R : ℝ) (a : Point) : Set Point := {z | sqDist z a ≤ R^2}
def cap (R : ℝ) (b : Point) : Set Point :=
  {z | sqDist z 0 ≤ R^2 ∧ sqDist z b < sqDist z 0}
def shadow (R : ℝ) (b : Point) : Set Point := {z | radialShadow R b z}

@[fun_prop]
lemma continuous_sqDist (a : Point) : Continuous (fun z => sqDist z a) := by
  unfold sqDist
  fun_prop

lemma disk_measurable (R : ℝ) (a : Point) : MeasurableSet (disk R a) :=
  measurableSet_le (continuous_sqDist a).measurable measurable_const

lemma cap_measurable (R : ℝ) (b : Point) : MeasurableSet (cap R b) :=
  (disk_measurable R 0).inter (measurableSet_lt (continuous_sqDist b).measurable
    (continuous_sqDist 0).measurable)

lemma shadow_measurable (R : ℝ) (b : Point) : MeasurableSet (shadow R b) := by
  have hh : Measurable (fun z : Point => ((R / Real.sqrt (sqDist z 0)) • z : Point)) := by
    have hf : Measurable (fun z : Point => R / Real.sqrt (sqDist z 0)) :=
      measurable_const.div (Real.continuous_sqrt.measurable.comp (continuous_sqDist 0).measurable)
    change Measurable ((fun z : Point => R / Real.sqrt (sqDist z 0)) • (id : Point → Point))
    exact hf.smul measurable_id
  exact (measurableSet_lt measurable_const (continuous_sqDist 0).measurable).inter
    ((disk_measurable R 0).inter (measurableSet_lt ((continuous_sqDist b).measurable.comp hh) measurable_const))

end PermCircles
