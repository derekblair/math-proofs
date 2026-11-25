import RadialMeasure
open MeasureTheory Set
open scoped ENNReal
namespace PermCircles
open Real

lemma disk_volume_origin {R : ℝ} (hR : 0 ≤ R) :
    volume (disk R 0) = ENNReal.ofReal (π*R^2) := by
  rw [polar_measure (disk_measurable R 0),domain_disk _ hR]
  have he : Ioc 0 R ×ˢ Ioo (-π) π = polarRegion (-π) π R (fun _ => 0) := by
    ext z
    exact and_comm
  rw [he]
  rw [region_slice measurable_const (fun _ _ => ⟨le_rfl,hR⟩)]
  simp only [zero_pow (by decide : 2 ≠ 0),sub_zero,setLIntegral_const,Real.volume_Ioo]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

#print axioms disk_volume_origin
end PermCircles
