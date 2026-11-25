import PlaneMeasure
import Rotation
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace PermCircles
open MeasureTheory Set

noncomputable def rotLin (c s : ℝ) : Point →ₗ[ℝ] Point :=
  Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ) !![c, s; -s, c]

lemma rotLin_apply (c s : ℝ) (z : Point) : rotLin c s z = rotate c s z := by
  rw [rotLin,Matrix.toLin_finTwoProd_apply]
  ext <;> simp [rotate] <;> ring

lemma det_rotLin (c s : ℝ) : (rotLin c s).det = c^2+s^2 := by
  rw [rotLin, LinearMap.det_toLin,Matrix.det_fin_two_of]
  ring

lemma volume_rot_preimage {c s : ℝ} (h : c^2+s^2=1) (S : Set Point) :
    volume (rotate c s ⁻¹' S) = volume S := by
  have h' : (rotLin c s).det = 1 := (det_rotLin c s).trans h
  have hr : rotate c s = rotLin c s := by funext z; exact (rotLin_apply c s z).symm
  rw [hr, Measure.addHaar_preimage_linearMap volume (show (rotLin c s).det ≠ 0 by simp [h']), h']
  simp

lemma volume_shadow_align {R d : ℝ} {b : Point} (hd : 0 < d) (h : sqDist b 0=d^2) :
    volume (shadow R b) = volume (shadow R (d,0)) := by
  have hn := alignment_isometry hd h
  have he : shadow R b = rotate (b.1/d) (b.2/d) ⁻¹' shadow R (d,0) := by
    ext z
    change radialShadow R b z ↔ radialShadow R (d,0) (rotate (b.1/d) (b.2/d) z)
    rw [←aligned hd h, shadow_rotate hn]
  rw [he, volume_rot_preimage hn]

lemma volume_cap_align {R d : ℝ} {b : Point} (hd : 0 < d) (h : sqDist b 0=d^2) :
    volume (cap R b) = volume (cap R (d,0)) := by
  have hn := alignment_isometry hd h
  have he : cap R b = rotate (b.1/d) (b.2/d) ⁻¹' cap R (d,0) := by
    ext z
    change (sqDist z 0≤R^2 ∧ sqDist z b<sqDist z 0) ↔
      (sqDist (rotate (b.1/d) (b.2/d) z) 0≤R^2 ∧
        sqDist (rotate (b.1/d) (b.2/d) z) (d,0) < sqDist (rotate (b.1/d) (b.2/d) z) 0)
    rw [← aligned hd h,rot_sq hn]
    have hz : sqDist (rotate (b.1/d) (b.2/d) z) 0 = sqDist z 0 := by
      simpa only [rot_zero] using rot_sq hn z 0
    rw [hz]
  rw [he, volume_rot_preimage hn]

#print axioms volume_cap_align
end PermCircles
