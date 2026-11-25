import CellSets
import RotateMeasure
import CapIntegral
import SectorNumeric

namespace PermCircles
open Real MeasureTheory Set Function
open scoped ENNReal BigOperators

noncomputable def capRatio : ℝ := 1-3*sqrt 3/(2*π)

lemma capRatio_nonneg : 0 ≤ capRatio := by
  have h := sin_le (show 0 ≤ π/3 by positivity)
  rw [sin_pi_div_three] at h
  unfold capRatio
  have he : 3*sqrt 3/(2*π) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  linarith

lemma cap_self (R : ℝ) : cap R (0 : Point) = ∅ := by
  ext z
  simp [cap]

lemma cap_volume_le_shadow {r R : ℝ} {b : Point} (hr : 0 < r) (hR : 0 < R)
    (he : R^2=4*r^2/3) (hdist : 4*r^2 ≤ sqDist b 0) :
    volume (cap R b) ≤ ENNReal.ofReal capRatio * volume (shadow R b) := by
  let d := sqrt (sqDist b 0)
  have hd0 : 0 < sqDist b 0 := lt_of_lt_of_le (by positivity) hdist 
  have hd : 0 < d := sqrt_pos.2 hd0
  have hds : sqDist b 0=d^2 := (sq_sqrt hd0.le).symm
  have hlow : 2*r ≤ d := by
    rw [hds] at hdist
    apply (sq_le_sq₀ (by positivity) hd.le).mp
    nlinarith
  rw [volume_cap_align hd hds, volume_shadow_align hd hds]
  by_cases hhigh : d ≤ 2*R
  · rw [cap_volume_aligned hR hd hhigh,shadow_volume_aligned hR hd hhigh,← ENNReal.ofReal_mul capRatio_nonneg]
    obtain ⟨h0,h1⟩ := half_width_bound hr hR he hlow hhigh
    apply ENNReal.ofReal_le_ofReal
    unfold capRatio
    have h := circle_cap_ratio (θ:=2*arccos (d/(2*R))) (R:=R) (by positivity) h1
    convert h using 1
    ring
  · have hempty : cap R (d,0) = ∅ := by
      ext z
      constructor
      · intro hz
        have hs := (cap_aligned hd z).mp hz.2
        have hRz : R < z.1 := by linarith
        have hmul := mul_pos (show 0 < z.1-R by linarith) (show 0 < z.1+R by linarith)
        have hq := hz.1
        simp [sqDist] at hq
        exact False.elim (by nlinarith [sq_nonneg z.2])
      · simp
    rw [hempty,measure_empty]
    exact bot_le

lemma volume_localCell_lower {I : Type*} [Fintype I] {r R : ℝ} (hr : 0<r)
    (hR : 0<R) (he : R^2=4*r^2/3) (p : I → Point)
    (hp : ∀ i j, i ≠ j → 4*r^2 ≤ sqDist (p i) (p j)) (i : I) :
    ENNReal.ofReal (2*sqrt 3*r^2) ≤ volume (localCell R p i) := by
  classical
  let S : I → Set Point := fun j => shadow R (p j-p i)
  let C : I → Set Point := fun j => cap R (p j-p i)
  have hS (j : I) : MeasurableSet (S j) := shadow_measurable R _
  have hdisk : volume (disk R 0) = ENNReal.ofReal (π*R^2) :=
    disk_volume_origin hR.le
  have hDfin : volume (disk R 0) ≠ ∞ := by rw [hdisk]; exact ENNReal.ofReal_ne_top
  have hcellfin : volume (localCell R p i) ≠ ∞ :=
    ne_top_of_le_ne_top hDfin (measure_mono fun _ h => h.1)
  have hU : (⋃ j, S j) ⊆ disk R 0 := by
    intro z hz
    rcases mem_iUnion.mp hz with ⟨j,hj⟩
    exact shadow_subdisk _ _ hj
  have hSsum := measure_mono hU (μ:=volume)
  rw [measure_iUnion (shadows_pairwise he p hp i) hS,tsum_fintype] at hSsum
  have hCtab (j : I) : volume (C j) ≤ ENNReal.ofReal capRatio * volume (S j) := by
    by_cases hij : j=i
    · subst j
      simp [C, cap_self]
    · have hb : 4*r^2 ≤ sqDist (p j-p i) 0 := by
        rw [← sub_self (p i),sqDist_translated]
        exact hp j i hij
      exact cap_volume_le_shadow hr hR he hb
  have hCsum : ∑ j, volume (C j) ≤ ENNReal.ofReal capRatio * volume (disk R 0) := by
    calc
      _ ≤ ∑ j, ENNReal.ofReal capRatio * volume (S j) := Finset.sum_le_sum fun j _ => hCtab j
      _ = ENNReal.ofReal capRatio * ∑ j, volume (S j) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hSsum (by positivity)
  have hu : volume (disk R 0) ≤ volume (localCell R p i)+
      ENNReal.ofReal capRatio * volume (disk R 0) := by
    calc
      _ ≤ volume (localCell R p i)+ volume (⋃ j, C j) := by
        rw [disk_cover_caps R p i]
        exact measure_union_le _ _
      _ ≤ volume (localCell R p i)+∑ j, volume (C j) := by
        have hc := measure_iUnion_le C (μ:=volume)
        rw [tsum_fintype] at hc
        exact add_le_add le_rfl hc
      _ ≤ _ := add_le_add le_rfl hCsum
  rw [hdisk,← ENNReal.ofReal_mul capRatio_nonneg] at hu
  have hfin : volume (localCell R p i) + ENNReal.ofReal (capRatio * (π*R^2)) ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hcellfin,ENNReal.ofReal_ne_top⟩
  have hreal := ENNReal.toReal_mono hfin hu
  rw [ENNReal.toReal_add hcellfin ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (mul_nonneg capRatio_nonneg (by positivity))] at hreal
  have hh := cell_constant r R he
  change π*R^2-capRatio*(π*R^2) = 2*sqrt 3*r^2 at hh
  have hex : 2*sqrt 3*r^2 ≤ (volume (localCell R p i)).toReal := by linarith
  rw [← ENNReal.ofReal_toReal hcellfin]
  exact ENNReal.ofReal_le_ofReal hex

#print axioms volume_localCell_lower
end PermCircles
