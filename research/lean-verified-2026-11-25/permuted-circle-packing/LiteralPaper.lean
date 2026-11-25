import Question55
import Interpretation

namespace PermCircles
open Filter MeasureTheory Real Set Function
open scoped ENNReal Topology BigOperators

def shift : Point := (1,1)

noncomputable def paperDensity {n : ℕ} (r : ℝ) (p : Equiv.Perm (Fin n)) : ℝ :=
  (∑ i, (volume (disk r (center p i+shift) ∩ box 1 (n:ℝ))).toReal) /
    (volume (box 1 (n:ℝ))).toReal

lemma paperDensity_eq {n : ℕ} (hn : 1 ≤ n) (r : ℝ) (p : Equiv.Perm (Fin n)) :
    paperDensity r p = clippedDensity r p := by
  have h₁ : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hpre : ∀ i, (fun z => z+shift) ⁻¹' (disk r (center p i+shift) ∩ box 1 (n:ℝ)) =
      disk r (center p i) ∩ box 0 ((n:ℝ)-1) := by
    intro i
    ext z
    change
      (sqDist (z+shift) (center p i+shift) ≤ r^2 ∧
        (1≤z.1+1 ∧ z.1+1≤(n:ℝ)) ∧ (1≤z.2+1 ∧ z.2+1≤(n:ℝ))) ↔
      (sqDist z (center p i) ≤ r^2 ∧
        (0≤z.1 ∧ z.1≤(n:ℝ)-1) ∧ (0≤z.2 ∧ z.2≤(n:ℝ)-1))
    rw [sqDist_shift,add_sub_cancel_right]
    constructor <;> rintro ⟨hs,⟨a,b⟩,c,d⟩ <;>
      exact ⟨hs,⟨by linarith,by linarith⟩,by linarith,by linarith⟩
  have hVol (i : Fin n) :
      volume (disk r (center p i+shift) ∩ box 1 (n:ℝ)) =
        volume (disk r (center p i) ∩ box 0 ((n:ℝ)-1)) := by
    rw [←hpre i,measure_preimage_add_right]
  unfold paperDensity clippedDensity areaOf
  rw [volume_box _ _ h₁,ENNReal.toReal_ofReal (by positivity)]
  simp_rw [hVol]

def PaperAdmissible {n : ℕ} (r : ℝ) (p : Equiv.Perm (Fin n)) : Prop :=
  Pairwise (Disjoint on fun i => interior (disk r (center p i+shift)))

def PaperMin {n : ℕ} (r : ℝ) (p : Equiv.Perm (Fin n)) : Prop :=
  2 ≤ n ∧ PaperAdmissible r p ∧
    ∀ m (q : Equiv.Perm (Fin m)), 2 ≤ m → PaperAdmissible r q → n ≤ m

lemma paper_separation {r : ℝ} (hr : 0<r) {n : ℕ} (p : Equiv.Perm (Fin n)) :
    PaperAdmissible r p ↔ ∀ i j, i ≠ j → 4*r^2 ≤ sqDist (center p i) (center p j) := by
  unfold PaperAdmissible Pairwise
  simp only [Function.onFun,disjoint_interiors_iff hr,sqDist_shift,add_sub_cancel_right]

lemma paperMin_iff {r : ℝ} (hr : 0<r) {n : ℕ} (p : Equiv.Perm (Fin n)) :
    PaperMin r p ↔ MinPacking r p := by
  unfold PaperMin MinPacking Fits
  simp only [paper_separation hr]
  constructor
  · rintro ⟨hn,hp,hm⟩
    exact ⟨hn,hp,fun m ⟨hg,q,hq⟩ => hm m q hg hq⟩
  · rintro ⟨hn,hp,hm⟩
    exact ⟨hn,hp,fun m q hg hq => hm m ⟨hg,q,hq⟩⟩

theorem question55_paper {n : ℝ → ℕ} (p : ∀ r, Equiv.Perm (Fin (n r)))
    (h : ∀ᶠ r in atTop, PaperMin r (p r)) :
    Tendsto (fun r => paperDensity r (p r)) atTop (𝓝 (π/(2*sqrt 3))) := by
  have hmin : ∀ᶠ r in atTop, MinPacking r (p r) := by
    filter_upwards [h,eventually_ge_atTop (1:ℝ)] with r hr h1
    exact (paperMin_iff (by linarith) _).mp hr
  apply (question55 p hmin).congr'
  filter_upwards [h] with r hr
  exact (paperDensity_eq (le_trans (by decide : 1 ≤ 2) hr.1) r (p r)).symm

/-- A literal singleton obeys the stated definition of permuted packing but has zero
    area for its clipping domain. It is excluded by the nondegenerate question. -/
theorem singleton_degenerate (r : ℝ) :
    PaperAdmissible r (Equiv.refl (Fin 1)) ∧ volume (box 1 1) = 0 := by
  constructor
  · intro i j hne
    exact False.elim (hne (Subsingleton.elim i j))
  · rw [volume_box _ _ le_rfl]
    norm_num

#print axioms question55_paper
#print axioms singleton_degenerate
end PermCircles
