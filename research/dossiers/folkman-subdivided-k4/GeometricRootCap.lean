import GeometricProductConditioning
import GeometricSphereTransitive

namespace RobustFolkman.GeometricGap
open MeasureTheory Set Matrix
open scoped ENNReal InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def capPoints (t : ℝ) (a : UnitSphere E) : Set (UnitSphere E) :=
  {x | t≤⟪(a:E),(x:E)⟫_ℝ}

theorem capPoints_measurable (t : ℝ) (a : UnitSphere E) :
    MeasurableSet (capPoints t a) :=
  measurableSet_le measurable_const (continuous_const.inner continuous_subtype_val).measurable

theorem sphere_open_mass_pos (s : Set (UnitSphere E)) (op : IsOpen s) (ne : s.Nonempty) :
    0<uniformSphere (volume : Measure E) s := by
  let v := (volume : Measure E).toSphere
  have p : 0<v s := op.measure_pos v ne
  have f : v univ≠∞ := measure_ne_top _ _
  unfold uniformSphere
  rw [Measure.smul_apply,smul_eq_mul]
  exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr f) p.ne'

theorem capPoints_both_positive (t : ℝ) (ta : -1<t) (tb : t<1) (a : UnitSphere E) :
    let σ := uniformSphere (volume : Measure E)
    0<σ (capPoints t a) ∧ 0<σ (capPoints t a)ᶜ := by
  intro σ
  have n : ‖(a:E)‖=1 := by simpa using a.property
  have one : ⟪(a:E),(a:E)⟫_ℝ=1 := by rw [real_inner_self_eq_norm_sq,n,one_pow]
  let s : Set (UnitSphere E) := {x | t<⟪(a:E),(x:E)⟫_ℝ}
  let q : Set (UnitSphere E) := {x | ⟪(a:E),(x:E)⟫_ℝ<t}
  have p : Continuous (fun x : UnitSphere E => ⟪(a:E),(x:E)⟫_ℝ) :=
    continuous_const.inner continuous_subtype_val
  have sn : s.Nonempty := ⟨a,by simpa [s,one] using tb⟩
  let b : UnitSphere E := ⟨-(a:E),by simpa [Metric.mem_sphere, dist_zero_right,n]⟩
  have qn : q.Nonempty := by
    refine ⟨b,?_⟩
    change ⟪(a:E),-(a:E)⟫_ℝ<t
    rw [inner_neg_right,one]
    exact ta
  refine ⟨(sphere_open_mass_pos s (isOpen_lt continuous_const p) sn).trans_le
    (measure_mono fun x (h : t< _) => h.le),?_⟩
  exact (sphere_open_mass_pos q (isOpen_lt p continuous_const) qn).trans_le
    (measure_mono fun x (h : _ < t) => not_le_of_gt h)

theorem capPoints_mass_root_constant (t : ℝ) (a b : UnitSphere E) :
    let σ := uniformSphere (volume : Measure E)
    σ (capPoints t a)=σ (capPoints t b) := by
  intro σ
  obtain ⟨e,h,p⟩ := uniformSphere_transitive a b
  have pre : (sphereRotation e) ⁻¹' capPoints t b=capPoints t a := by
    ext x
    have bv : (b:E)=e a := by rw [←h,sphereRotation_val]
    change t≤⟪(b:E),(sphereRotation e x:E)⟫_ℝ ↔ t≤⟪(a:E),(x:E)⟫_ℝ
    rw [bv,sphereRotation_val,e.inner_map_map]
  have m := p.measure_preimage (capPoints_measurable t b).nullMeasurableSet
  rwa [pre] at m

#print axioms capPoints_both_positive
#print axioms capPoints_mass_root_constant
end RobustFolkman.GeometricGap
