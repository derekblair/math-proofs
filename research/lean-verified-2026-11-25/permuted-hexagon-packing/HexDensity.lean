import LowerBound
import FiniteIndices

namespace PermHex
open Set MeasureTheory
open scoped ENNReal BigOperators
open PermCircles (box good_bounds card_good good)

lemma good_unclipped {c s r : ℝ} {n m : ℕ} (hU : c^2+s^2=1) (hr : 0≤r)
    (hm : 4*r≤(m:ℝ)) {p : Equiv.Perm (Fin n)} {i : Fin n} (hi : i∈good m p) :
    atCenter true c s r (center p i) ⊆ box 0 ((n:ℝ)-1) := by
  obtain ⟨h1,h2,h3,h4⟩ := good_bounds hi
  have h₁ : (m:ℝ)≤(i.val:ℝ) := by exact_mod_cast h1
  have h₂ : (m:ℝ)≤((p i).val:ℝ) := by exact_mod_cast h2
  have h₃ : (m:ℝ)+(i.val:ℝ)+1≤n := by
    have h := i.isLt
    exact_mod_cast (show m+i.val+1≤n by omega)
  have h₄ : (m:ℝ)+((p i).val:ℝ)+1≤n := by
    have h := (p i).isLt
    exact_mod_cast (show m+(p i).val+1≤n by omega)
  intro z hz
  have h := (atCenter_closed_iff c s r (center p i) z).1 hz
  obtain ⟨ha,hb⟩ := gauge_rotated_cube hU hr h
  have hx : |z.1-(i.val:ℝ)|≤4*r := ha
  have hy : |z.2-((p i).val:ℝ)|≤4*r := hb
  rcases abs_le.mp hx with ⟨a,b⟩
  rcases abs_le.mp hy with ⟨d,e⟩
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

noncomputable def areaWithin {n : ℕ} (c s r : ℝ) (p : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  (volume (atCenter true c s r (center p i) ∩ box 0 ((n:ℝ)-1))).toReal

noncomputable def clippedDensity {n : ℕ} (c s r : ℝ) (p : Equiv.Perm (Fin n)) : ℝ :=
  (∑ i, areaWithin c s r p i)/((n:ℝ)-1)^2

lemma areaWithin_le {c s r : ℝ} (hU : c^2+s^2=1) (hr : 0≤r) {n : ℕ}
    (p : Equiv.Perm (Fin n)) (i : Fin n) :
    areaWithin c s r p i ≤ areaUnit*r^2 := by
  have hd : volume (atCenter true c s r (center p i)) ≠ ∞ := by
    rw [atCenter_volume hU true hr]
    exact ENNReal.ofReal_ne_top
  have h := ENNReal.toReal_mono hd (measure_mono (inter_subset_left :
    atCenter true c s r (center p i) ∩ box 0 ((n:ℝ)-1) ⊆ atCenter true c s r (center p i)))
  rwa [atCenter_volume hU true hr,ENNReal.toReal_ofReal (by have := areaUnit_pos; positivity)] at h

lemma areaWithin_good {c s r : ℝ} (hU : c^2+s^2=1) (hr : 0≤r) {n m : ℕ}
    (hm : 4*r≤(m:ℝ)) {p : Equiv.Perm (Fin n)} {i : Fin n} (hi : i∈good m p) :
    areaWithin c s r p i = areaUnit*r^2 := by
  unfold areaWithin
  rw [inter_eq_left.mpr (good_unclipped hU hr hm hi),atCenter_volume hU true hr,
    ENNReal.toReal_ofReal (by have := areaUnit_pos; positivity)]

theorem density_bounds {c s r : ℝ} (hU : c^2+s^2=1) (hr : 1≤r) {n : ℕ}
    (p : Equiv.Perm (Fin n)) :
    areaUnit*r^2*((n:ℝ)-16*r-4)/((n:ℝ)-1)^2≤clippedDensity c s r p ∧
    clippedDensity c s r p≤areaUnit*r^2*(n:ℝ)/((n:ℝ)-1)^2 := by
  let m := (⌈4*r⌉:ℤ).toNat
  have hm0 : 0≤(⌈4*r⌉:ℤ) := by
    have hh := Int.le_ceil (4*r)
    exact_mod_cast (show 0≤((⌈4*r⌉:ℤ):ℝ) by linarith)
  have hmcast : (m:ℝ)=((⌈4*r⌉:ℤ):ℝ) := by
    have hh : (m:ℤ)=⌈4*r⌉ := Int.toNat_of_nonneg hm0
    exact_mod_cast hh
  have hm : 4*r≤(m:ℝ) := by rw [hmcast]; exact Int.le_ceil _
  have hmu : (m:ℝ)≤4*r+1 := by rw [hmcast]; exact (Int.ceil_lt_add_one _).le
  have hCard : (n:ℝ)≤((good m p).card:ℝ)+4*(m:ℝ) := by exact_mod_cast card_good (m:=m) p
  have hl : (n:ℝ)-16*r-4≤((good m p).card:ℝ) := by linarith
  have hArea0 : 0≤areaUnit*r^2 := by have := areaUnit_pos; positivity
  constructor
  · apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    calc
      areaUnit*r^2*((n:ℝ)-16*r-4)≤areaUnit*r^2*((good m p).card:ℝ) :=
        mul_le_mul_of_nonneg_left hl hArea0
      _ = ∑ i∈good m p, areaWithin c s r p i := by
        rw [Finset.sum_congr rfl (fun _ hi => areaWithin_good hU (by linarith) hm hi)]
        simp [mul_comm]
      _ ≤ ∑ i, areaWithin c s r p i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => ENNReal.toReal_nonneg)
  · apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    calc
      ∑ i, areaWithin c s r p i≤∑ _ : Fin n, areaUnit*r^2 :=
        Finset.sum_le_sum (fun i _ => areaWithin_le hU (by linarith) p i)
      _ = _ := by simp [mul_comm]

#print axioms density_bounds
end PermHex
