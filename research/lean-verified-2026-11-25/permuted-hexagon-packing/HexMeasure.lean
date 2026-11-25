import DetBound
import PlaneMeasure
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace PermHex
open MeasureTheory Filter Set
open scoped ENNReal

def strip (closed : Bool) (a b : ℝ) : Set ℝ :=
  if closed then Icc a b else Ioo a b

lemma strip_meas (closed : Bool) (a b : ℝ) : MeasurableSet (strip closed a b) := by
  cases closed <;> simp [strip]

lemma volume_strip (closed : Bool) (a b : ℝ) : volume (strip closed a b)=ENNReal.ofReal (b-a) := by
  cases closed <;> simp [strip,Real.volume_Icc,Real.volume_Ioo]

noncomputable def halfw (t : ℝ) : ℝ := root3*t/2
noncomputable def height (t x : ℝ) : ℝ := t-|x|/root3
def tile (closed : Bool) (t : ℝ) : Set Point :=
    {z | z.1∈strip closed (-halfw t) (halfw t) ∧ z.2∈strip closed (-height t z.1) (height t z.1)}

lemma height_cont (t : ℝ) : Continuous (height t) := by
  unfold height
  fun_prop

lemma tile_meas (closed : Bool) (t : ℝ) : MeasurableSet (tile closed t) := by
  have hm : Measurable fun z : Point => height t z.1 :=
    (height_cont t).measurable.comp measurable_fst
  apply (measurable_fst (strip_meas closed _ _)).inter
  cases closed
  · exact (measurableSet_lt hm.neg measurable_snd).inter (measurableSet_lt measurable_snd hm)
  · exact (measurableSet_le hm.neg measurable_snd).inter (measurableSet_le measurable_snd hm)

lemma tile_closed_iff (t : ℝ) (z : Point) : z∈tile true t ↔ gauge z≤t := by
  have hS := root3_pos
  change ((-halfw t≤z.1 ∧ z.1≤halfw t) ∧ (-height t z.1≤z.2 ∧ z.2≤height t z.1)) ↔ _
  rw [←abs_le,←abs_le]
  unfold gauge halfw height
  rw [max_le_iff,div_le_iff₀ hS]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

lemma tile_open_iff (t : ℝ) (z : Point) : z∈tile false t ↔ gauge z<t := by
  have hS := root3_pos
  change ((-halfw t<z.1 ∧ z.1<halfw t) ∧ (-height t z.1<z.2 ∧ z.2<height t z.1)) ↔ _
  rw [←abs_lt,←abs_lt]
  unfold gauge halfw height
  rw [max_lt_iff,div_lt_iff₀ hS]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

lemma slice_eq (closed : Bool) (t x : ℝ) (hx : x∈strip closed (-halfw t) (halfw t)) :
    (Prod.mk x) ⁻¹' tile closed t = strip closed (-height t x) (height t x) := by
  ext y
  change (x∈strip closed (-halfw t) (halfw t) ∧ _) ↔ _
  simp [hx]

lemma tile_lintegral (closed : Bool) (t : ℝ) :
    volume (tile closed t) =
      ∫⁻ x in strip closed (-halfw t) (halfw t), ENNReal.ofReal (2*height t x) := by
  change (volume : Measure ℝ).prod (volume : Measure ℝ) (tile closed t) = _
  rw [Measure.prod_apply (tile_meas _ _), ← lintegral_indicator (strip_meas closed _ _)]
  apply lintegral_congr
  intro x
  by_cases hx : x∈strip closed (-halfw t) (halfw t)
  · rw [slice_eq closed t x hx,volume_strip,indicator_of_mem hx]
    congr 1
    ring
  · rw [indicator_of_notMem hx]
    have he : (Prod.mk x) ⁻¹' tile closed t = ∅ := by
      ext y
      change (x∈strip closed (-halfw t) (halfw t) ∧ _) ↔ _
      simp [hx]
    rw [he,measure_empty]

lemma strip_hr {closed : Bool} {t x : ℝ} (hx : x∈strip closed (-halfw t) (halfw t)) :
    |x|≤halfw t := by
  cases closed
  · exact le_of_lt (abs_lt.mpr hx)
  · exact abs_le.mpr hx

lemma height_nonneg {closed : Bool} {t x : ℝ} (ht : 0≤t)
    (hx : x∈strip closed (-halfw t) (halfw t)) : 0≤height t x := by
  have hp := root3_pos
  have h := strip_hr hx
  have hr : |x|/root3≤t/2 := by
    apply (div_le_iff₀ hp).2
    unfold halfw at h
    linarith
  unfold height
  linarith

lemma interval_linear (a b u v : ℝ) :
    ∫ x in a..b, u*x+v = u*((b^2-a^2)/2)+v*(b-a) := by
  have hc : Continuous (fun x : ℝ => u*x) := by fun_prop
  have hc' : Continuous (fun _ : ℝ => v) := continuous_const
  rw [intervalIntegral.integral_add (hc.intervalIntegrable ..) (hc'.intervalIntegrable ..),
    intervalIntegral.integral_const_mul,integral_id,intervalIntegral.integral_const]
  simp [smul_eq_mul]
  ring

lemma interval_height {t : ℝ} (ht : 0≤t) :
    ∫ x in -halfw t..halfw t, 2*height t x = areaUnit*t^2 := by
  let a := halfw t
  have hroot := root3_pos
  have ha : 0≤a := by dsimp [a,halfw]; positivity
  have h₁ : ∫ x in -a..(0:ℝ), 2*height t x = ∫ x in -a..(0:ℝ), (2/root3)*x+2*t := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le (by linarith : -a≤0)]
    intro x hx
    change 2*(t-|x|/root3)=(2/root3)*x+2*t
    rw [abs_of_nonpos hx.2]
    ring
  have h₂ : ∫ x in (0:ℝ)..a, 2*height t x = ∫ x in (0:ℝ)..a, (-2/root3)*x+2*t := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le ha]
    intro x hx
    change 2*(t-|x|/root3)=(-2/root3)*x+2*t
    rw [abs_of_nonneg hx.1]
    ring
  have hc : Continuous (fun x => 2*height t x) := (height_cont t).const_mul _
  change ∫ x in -a..a, 2*height t x = _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-a) 0)
    (hc.intervalIntegrable 0 a),h₁,h₂,interval_linear,interval_linear]
  unfold areaUnit
  dsimp [a,halfw]
  field_simp [hroot.ne'] <;> ring

theorem volume_tile (closed : Bool) (t : ℝ) (ht : 0≤t) :
    volume (tile closed t)=ENNReal.ofReal (areaUnit*t^2) := by
  have ha : 0≤halfw t := by have := root3_pos; unfold halfw; positivity
  have hab : -halfw t≤halfw t := by linarith
  have hc : Continuous (fun x => 2*height t x) := (height_cont t).const_mul _
  have hi : IntegrableOn (fun x => 2*height t x) (strip closed (-halfw t) (halfw t)) volume := by
    have hI : IntegrableOn (fun x => 2*height t x) (Icc (-halfw t) (halfw t)) volume :=
      hc.continuousOn.integrableOn_compact isCompact_Icc
    cases closed
    · exact hI.mono_set Ioo_subset_Icc_self
    · exact hI
  have hn : 0≤ᵐ[volume.restrict (strip closed (-halfw t) (halfw t))] (fun x => 2*height t x) := by
    filter_upwards [ae_restrict_mem (strip_meas closed _ _)] with x hx
    exact mul_nonneg (by norm_num) (height_nonneg ht hx)
  rw [tile_lintegral, ← ofReal_integral_eq_lintegral_ofReal hi hn]
  have he : ∫ x in strip closed (-halfw t) (halfw t), 2*height t x =
      ∫ x in -halfw t..halfw t, 2*height t x := by
    rw [intervalIntegral.integral_of_le hab]
    cases closed
    · exact integral_Ioc_eq_integral_Ioo.symm
    · exact integral_Icc_eq_integral_Ioc
  rw [he,interval_height ht]

#print axioms volume_tile
end PermHex
