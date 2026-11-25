import HexMeasure
import RotateMeasure

namespace PermHex
open Filter MeasureTheory Set
open scoped ENNReal Topology
open PermCircles (rotate)

@[fun_prop]
lemma continuous_gauge : Continuous gauge := by
  unfold gauge
  fun_prop

@[fun_prop]
lemma continuous_rotate (c s : ℝ) : Continuous (rotate c s) := by
  unfold rotate
  fun_prop

@[fun_prop]
lemma continuous_gaugeR (c s : ℝ) : Continuous (gaugeR c s) :=
  continuous_gauge.comp (continuous_rotate c s)

lemma gaugeR_neg (c s : ℝ) (z : Point) : gaugeR c s (-z)=gaugeR c s z := by
  rw [show -z=(-1:ℝ) • z by simp,gaugeR_smul]
  norm_num

def body (closed : Bool) (c s t : ℝ) : Set Point := rotate c s ⁻¹' tile closed t

lemma body_closed_iff (c s t : ℝ) (z : Point) :
    z∈body true c s t ↔ gaugeR c s z≤t := tile_closed_iff _ _

lemma body_open_iff (c s t : ℝ) (z : Point) :
    z∈body false c s t ↔ gaugeR c s z<t := tile_open_iff _ _

lemma body_meas (b : Bool) (c s t : ℝ) : MeasurableSet (body b c s t) :=
  (continuous_rotate c s).measurable (tile_meas b t)

lemma body_volume {c s : ℝ} (hU : c^2+s^2=1) (b : Bool) {t : ℝ} (ht : 0≤t) :
    volume (body b c s t)=ENNReal.ofReal (areaUnit*t^2) := by
  unfold body
  rw [PermCircles.volume_rot_preimage hU,volume_tile b t ht]

lemma body_open_subset (c s t : ℝ) : body false c s t ⊆ body true c s t :=
  fun z hz => (body_closed_iff c s t z).2 ((body_open_iff c s t z).1 hz).le

lemma interior_body {c s t : ℝ} (ht : 0<t) :
    interior (body true c s t)=body false c s t := by
  apply le_antisymm
  · intro z hz
    apply (body_open_iff c s t z).2
    by_contra! hnot
    have hq : gaugeR c s z=t :=
      le_antisymm ((body_closed_iff c s t z).1 (interior_subset hz)) hnot
    let A : Set ℝ := (fun r : ℝ => r • z) ⁻¹' interior (body true c s t)
    have hAo : IsOpen A := isOpen_interior.preimage ((continuous_id : Continuous (id : ℝ→ℝ)).smul continuous_const)
    have hA1 : (1:ℝ)∈A := by simpa [A] using hz
    obtain ⟨a,b,⟨ha,hb⟩,hI⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hAo.mem_nhds hA1)
    let r := (1+b)/2
    have hr1 : 1<r := by dsimp [r]; linarith
    have hrb : r<b := by dsimp [r]; linarith
    have hrA : r∈A := hI ⟨ha.trans hr1,hrb⟩
    have hq' : gaugeR c s (r • z)≤t :=
      (body_closed_iff c s t _).mp (interior_subset hrA)
    rw [gaugeR_smul,abs_of_nonneg (by linarith),hq] at hq'
    have hm := mul_pos (show 0<r-1 by linarith) ht
    nlinarith
  · apply interior_maximal (body_open_subset c s t)
    have he : body false c s t={z | gaugeR c s z<t} := by ext z; exact body_open_iff _ _ _ _
    rw [he]
    exact isOpen_lt (continuous_gaugeR c s) continuous_const

def atCenter (closed : Bool) (c s t : ℝ) (a : Point) : Set Point :=
  (fun z => z+(-a)) ⁻¹' body closed c s t

lemma atCenter_closed_iff (c s t : ℝ) (a z : Point) :
    z∈atCenter true c s t a ↔ gaugeR c s (z-a)≤t := by
  change (z+(-a))∈body true c s t ↔ _
  rw [body_closed_iff,sub_eq_add_neg]

lemma atCenter_open_iff (c s t : ℝ) (a z : Point) :
    z∈atCenter false c s t a ↔ gaugeR c s (z-a)<t := by
  change (z+(-a))∈body false c s t ↔ _
  rw [body_open_iff,sub_eq_add_neg]

lemma atCenter_volume {c s : ℝ} (hU : c^2+s^2=1) (b : Bool) {t : ℝ} (ht : 0≤t) (a : Point) :
    volume (atCenter b c s t a)=ENNReal.ofReal (areaUnit*t^2) := by
  unfold atCenter
  rw [measure_preimage_add_right,body_volume hU b ht]

lemma atCenter_meas (b : Bool) (c s t : ℝ) (a : Point) :
    MeasurableSet (atCenter b c s t a) :=
  (measurable_id.add measurable_const) (body_meas b c s t)

lemma interior_atCenter {c s t : ℝ} (ht : 0<t) (a : Point) :
    interior (atCenter true c s t a)=atCenter false c s t a := by
  let T : Point ≃ₜ Point := Homeomorph.addRight (-a)
  change interior (T ⁻¹' body true c s t)=T ⁻¹' body false c s t
  rw [← T.preimage_interior,interior_body ht]

theorem separation_iff {c s t : ℝ} (ht : 0<t) (p q : Point) :
    Disjoint (interior (atCenter true c s t p)) (interior (atCenter true c s t q)) ↔
    2*t≤gaugeR c s (p-q) := by
  rw [interior_atCenter ht,interior_atCenter ht]
  constructor
  · intro h
    by_contra! hh
    let z : Point := ((1/2:ℝ) • (p+q))
    have heq : z-q=(1/2:ℝ) • (p-q) := by
      apply Prod.ext <;> simp [z] <;> ring
    have hep : z-p=(-1/2:ℝ) • (p-q) := by
      apply Prod.ext <;> simp [z] <;> ring
    have hp : z∈atCenter false c s t p := by
      apply (atCenter_open_iff c s t _ _).2
      rw [hep,gaugeR_smul]
      norm_num
      linarith
    have hq : z∈atCenter false c s t q := by
      apply (atCenter_open_iff c s t _ _).2
      rw [heq,gaugeR_smul]
      norm_num
      linarith
    exact disjoint_left.mp h hp hq
  · intro h
    apply disjoint_left.mpr
    intro z hz1 hz2
    have hp := (atCenter_open_iff c s t _ _).1 hz1
    have hq := (atCenter_open_iff c s t _ _).1 hz2
    have he := gaugeR_triangle c s (p-z) (z-q)
    rw [sub_add_sub_cancel,show p-z= -(z-p) by abel,gaugeR_neg] at he
    linarith

#print axioms separation_iff
end PermHex
