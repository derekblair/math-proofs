import GeometricCapTangentMoment
import GeometricSphericalCompare

namespace RobustFolkman.GeometricGap
open MeasureTheory Set WithLp
open scoped ENNReal InnerProductSpace

theorem slice_double_tail (r t : ℝ) (r3 : 3≤r) (tp : 0<t) (t1 : t≤1/8)
    (dense : 1≤4*r*t^2) :
    sliceMass r (2*t) 1 ≤ ENNReal.ofReal (Real.exp (3-2*r*t^2))*sliceMass r t 1 := by
  have rp : 0<r := by linarith
  have wid : 1/(4*r*t)≤1-t := by
    have h : 1/(4*r*t)≤t := (div_le_iff₀ (by positivity)).2 (by nlinarith only [dense])
    linarith only [h,t1]
  have lo := slice_mass_band_lower r t (1-t) r3 tp t1 dense wid
  rw [add_sub_cancel] at lo
  refine (slice_mass_cap_upper r (2*t) rp (by positivity) (by linarith only [t1])).trans ?_
  have w := slice_weight_upper_exp r t (2*t) rp tp.le (by linarith) (by linarith) (by linarith)
  have w' : sliceWeight r (2*t)/(2*r*(2*t)) ≤
      (Real.exp (3-2*r*t^2))*(Real.exp (-3)*sliceWeight r t/(4*r*t)) := by
    have eq : (Real.exp (3-2*r*t^2))*(Real.exp (-3)*sliceWeight r t/(4*r*t)) =
      (Real.exp (-2*r*t^2)*sliceWeight r t)/(2*r*(2*t)) := by
      rw [←mul_div_assoc,←mul_assoc,←Real.exp_add]
      rw [show 3-2*r*t^2 + -3= -2*r*t^2 by ring]
      congr 1
      ring
    rw [eq]
    have wE : -(2*r*t)*(2*t-t)= -2*r*t^2 := by ring
    rw [wE] at w
    exact div_le_div_of_nonneg_right w (by positivity)
  refine (ENNReal.ofReal_le_ofReal w').trans ?_
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  gcongr

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem cap_double_height_tail (n : ℕ) (dim : Module.finrank ℝ E=n+3)
    (t : ℝ) (tp : 0<t) (t1 : t≤1/8)
    (large : 3≤(n:ℝ)/2) (dense : 1≤4*((n:ℝ)/2)*t^2)
    (a : UnitSphere E) :
    let σ := uniformSphere (volume : Measure E)
    σ (capPoints (2*t) a) ≤
      ENNReal.ofReal (Real.exp (3-2*((n:ℝ)/2)*t^2))*σ (capPoints t a) := by
  intro σ
  obtain ⟨K,e,he,hD⟩ := root_shell_isometry a
  let W := ↥Kᗮ
  have D : Module.finrank ℝ W=n+2 := by dsimp [W]; omega
  letI : Nontrivial W := Module.nontrivial_of_finrank_pos (R:=ℝ) (by omega)
  letI : Nontrivial (SphereAmbient (Fin 1) W) := e.injective.nontrivial
  let f := sphereTransport e
  let τ := uniformSphere (volume : Measure (SphereAmbient (Fin 1) W))
  have F : MeasurePreserving f σ τ := sphereTransport_volume e
  have eq (x : ℝ) (h : 0≤x) :
      σ (capPoints x a) = sliceMass ((n:ℝ)/2) x 1/sliceMass ((n:ℝ)/2) (-1) 1 := by
    let P := sphereHeight (W:=W) ⁻¹' Ici x
    have Pm : MeasurableSet P := sphereHeight_measurable measurableSet_Ici
    have pp : f ⁻¹' P=capPoints x a := by ext y; exact (show (x≤sphereHeight (f y)) ↔ _ by rw [he y]; rfl)
    have HH := F.measure_preimage Pm.nullMeasurableSet
    rw [pp] at HH
    change _=τ (sphereHeight ⁻¹' Ici x) at HH
    rw [HH,cap_height_preimage]
    exact spherical_height_interval n D x 1 (by linarith) le_rfl
  rw [eq (2*t) (by positivity),eq t tp.le]
  have bd := slice_double_tail ((n:ℝ)/2) t large tp t1 dense
  simp only [ENNReal.div_eq_inv_mul]
  calc
    _ ≤ _ * (_*sliceMass ((n:ℝ)/2) t 1) := by gcongr
    _ = _ := by ac_rfl

#print axioms cap_double_height_tail
end RobustFolkman.GeometricGap
