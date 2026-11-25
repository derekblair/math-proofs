import CellArrangement
import FiniteIndices
import DiskMeasure

namespace PermCircles
open MeasureTheory Set Real
open scoped ENNReal BigOperators

def center {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) : Point :=
  ((i.val:ℝ),((p i).val:ℝ))

lemma centers_fst_injective {n : ℕ} (p : Equiv.Perm (Fin n)) :
    Function.Injective fun i => (center p i).1 := by
  intro i j h
  apply Fin.ext
  change (i.val:ℝ) = (j.val:ℝ) at h
  exact_mod_cast h

lemma centers_in_box {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) :
    center p i ∈ box 0 ((n:ℝ)-1) := by
  have h1 : (i.val:ℝ)+1 ≤ n := by
    exact_mod_cast (show i.val+1 ≤ n from i.isLt)
  have h2 : ((p i).val:ℝ)+1 ≤ n := by
    exact_mod_cast (show (p i).val+1 ≤ n from (p i).isLt)
  change ((0:ℝ) ≤ (i.val:ℝ) ∧ (i.val:ℝ) ≤ (n:ℝ)-1) ∧
    ((0:ℝ) ≤ ((p i).val:ℝ) ∧ ((p i).val:ℝ) ≤ (n:ℝ)-1)
  exact ⟨⟨by positivity, by linarith⟩, ⟨by positivity,by linarith⟩⟩

lemma disk_volume {r : ℝ} (hr : 0 ≤ r) (c : Point) :
    volume (disk r c) = ENNReal.ofReal (π*r^2) := by
  have he : disk r 0 = (fun z => z+c) ⁻¹' disk r c := by
    ext z
    change (sqDist z 0≤r^2) ↔ sqDist (z+c) c≤r^2
    simp [sqDist_shift]
  have hh := disk_volume_origin hr
  rw [he,measure_preimage_add_right] at hh
  exact hh

lemma good_unclipped {r : ℝ} {n m : ℕ} (hr : 0≤r) (hm : r ≤ (m:ℝ))
    {p : Equiv.Perm (Fin n)} {i : Fin n} (hi : i ∈ good m p) :
    disk r (center p i) ⊆ box 0 ((n:ℝ)-1) := by
  obtain ⟨h1,h2,h3,h4⟩ := good_bounds hi
  have h₁ : (m:ℝ) ≤ (i.val:ℝ) := by exact_mod_cast h1
  have h₂ : (m:ℝ) ≤ ((p i).val:ℝ) := by exact_mod_cast h2
  have h₃ : (m:ℝ)+(i.val:ℝ)+1 ≤ n := by
    have hn := i.isLt
    exact_mod_cast (show m+i.val+1 ≤ n by omega)
  have h₄ : (m:ℝ)+((p i).val:ℝ)+1 ≤ n := by
    have hn := (p i).isLt
    exact_mod_cast (show m+(p i).val+1 ≤ n by omega)
  intro z hz
  change (z.1-(i.val:ℝ))^2+(z.2-((p i).val:ℝ))^2 ≤ r^2 at hz
  have hA : |z.1-(i.val:ℝ)| ≤ r := by
    apply (sq_le_sq₀ (abs_nonneg _) hr).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (z.2-((p i).val:ℝ))]
  have hB : |z.2-((p i).val:ℝ)| ≤ r := by
    apply (sq_le_sq₀ (abs_nonneg _) hr).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (z.1-(i.val:ℝ))]
  rcases abs_le.mp hA with ⟨a,b⟩
  rcases abs_le.mp hB with ⟨c,d⟩
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

noncomputable def areaOf {n : ℕ} (r : ℝ) (p : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  (volume (disk r (center p i) ∩ box 0 ((n:ℝ)-1))).toReal

noncomputable def clippedDensity {n : ℕ} (r : ℝ) (p : Equiv.Perm (Fin n)) : ℝ :=
  (∑ i, areaOf r p i)/((n:ℝ)-1)^2

lemma areaOf_le {n : ℕ} {r : ℝ} (hr : 0 ≤ r) (p : Equiv.Perm (Fin n)) (i : Fin n) :
    areaOf r p i ≤ π*r^2 := by
  have hd : volume (disk r (center p i)) ≠ ∞ := by
    rw [disk_volume hr]
    exact ENNReal.ofReal_ne_top
  have h := ENNReal.toReal_mono hd (measure_mono (inter_subset_left :
    disk r (center p i) ∩ box 0 ((n:ℝ)-1) ⊆ disk r (center p i)))
  rwa [disk_volume hr,ENNReal.toReal_ofReal (by positivity)] at h

lemma areaOf_good {n m : ℕ} {r : ℝ} (hr : 0 ≤ r) (hm : r ≤ (m:ℝ))
    {p : Equiv.Perm (Fin n)} {i : Fin n} (hi : i ∈ good m p) :
    areaOf r p i = π*r^2 := by
  unfold areaOf
  rw [inter_eq_left.mpr (good_unclipped hr hm hi),disk_volume hr,ENNReal.toReal_ofReal (by positivity)]

lemma density_bounds {n : ℕ} {r : ℝ} (hr : 1 ≤ r) (p : Equiv.Perm (Fin n)) :
    π*r^2*((n:ℝ)-4*r-4)/((n:ℝ)-1)^2 ≤ clippedDensity r p ∧
    clippedDensity r p ≤ π*r^2*(n:ℝ)/((n:ℝ)-1)^2 := by
  let m := (⌈r⌉ : ℤ).toNat
  have hm0 : 0 ≤ (⌈r⌉ : ℤ) := by
    have hh := Int.le_ceil r
    exact_mod_cast (show 0 ≤ ((⌈r⌉ : ℤ) : ℝ) by linarith)
  have hmcast : (m:ℝ) = ((⌈r⌉ : ℤ):ℝ) := by
    have hh : (m:ℤ) = ⌈r⌉ := Int.toNat_of_nonneg hm0
    exact_mod_cast hh
  have hm : r ≤ (m:ℝ) := by rw [hmcast]; exact Int.le_ceil _
  have hmu : (m:ℝ) ≤ r+1 := by rw [hmcast]; exact (Int.ceil_lt_add_one r).le
  have hCard : (n:ℝ) ≤ ((good m p).card:ℝ) + 4*(m:ℝ) := by exact_mod_cast card_good (m:=m) p
  have hlowCard : (n:ℝ)-4*r-4 ≤ ((good m p).card:ℝ) := by linarith
  constructor
  · apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    calc
      π*r^2*((n:ℝ)-4*r-4) ≤ π*r^2*((good m p).card:ℝ) :=
        mul_le_mul_of_nonneg_left hlowCard (by positivity)
      _ = ∑ i ∈ good m p, areaOf r p i := by
        rw [Finset.sum_congr rfl (fun _ hi => areaOf_good (by linarith) hm hi)]
        simp [mul_comm]
      _ ≤ ∑ i, areaOf r p i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => ENNReal.toReal_nonneg)
  · apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    calc
      ∑ i, areaOf r p i ≤ ∑ _ : Fin n, π*r^2 := Finset.sum_le_sum (fun i _ => areaOf_le (by linarith) p i)
      _ = _ := by simp [mul_comm]

#print axioms density_bounds
end PermCircles
