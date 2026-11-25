import HexLimit

namespace PermHex
open Filter MeasureTheory Set Function
open scoped ENNReal Topology BigOperators
open PermCircles (box volume_box)

def shift : Point := (1,1)

noncomputable def paperDensity {n : ℕ} (c s t : ℝ) (p : Equiv.Perm (Fin n)) : ℝ :=
  (∑ i, (volume (atCenter true c s t (center p i+shift) ∩ box 1 (n:ℝ))).toReal) /
    (volume (box 1 (n:ℝ))).toReal

lemma paperDensity_eq {n : ℕ} (hn : 1≤n) (c s t : ℝ) (p : Equiv.Perm (Fin n)) :
    paperDensity c s t p = clippedDensity c s t p := by
  have h₁ : (1:ℝ)≤n := by exact_mod_cast hn
  have hpre : ∀ i, (fun z => z+shift) ⁻¹' (atCenter true c s t (center p i+shift) ∩ box 1 (n:ℝ)) =
      atCenter true c s t (center p i) ∩ box 0 ((n:ℝ)-1) := by
    intro i
    ext z
    change ((z+shift)∈atCenter true c s t (center p i+shift) ∧
      (1≤z.1+1 ∧ z.1+1≤(n:ℝ)) ∧ (1≤z.2+1 ∧ z.2+1≤(n:ℝ))) ↔
      (z∈atCenter true c s t (center p i) ∧
      (0≤z.1 ∧ z.1≤(n:ℝ)-1) ∧ (0≤z.2 ∧ z.2≤(n:ℝ)-1))
    rw [atCenter_closed_iff,atCenter_closed_iff,add_sub_add_right_eq_sub]
    constructor <;> rintro ⟨h,⟨a,b⟩,d,e⟩ <;>
      exact ⟨h,⟨by linarith,by linarith⟩,by linarith,by linarith⟩
  have hVol (i : Fin n) :
      volume (atCenter true c s t (center p i+shift) ∩ box 1 (n:ℝ)) =
        volume (atCenter true c s t (center p i) ∩ box 0 ((n:ℝ)-1)) := by
    rw [←hpre i,measure_preimage_add_right]
  unfold paperDensity clippedDensity areaWithin
  rw [volume_box _ _ h₁,ENNReal.toReal_ofReal (by positivity)]
  simp_rw [hVol]

def PaperAdmissible {n : ℕ} (c s t : ℝ) (p : Equiv.Perm (Fin n)) : Prop :=
  Pairwise (Disjoint on fun i => interior (atCenter true c s t (center p i+shift)))

def PaperMin {n : ℕ} (c s t : ℝ) (p : Equiv.Perm (Fin n)) : Prop :=
  2≤n ∧ PaperAdmissible c s t p ∧
    ∀ m (q : Equiv.Perm (Fin m)), 2≤m → PaperAdmissible c s t q → n≤m

lemma paper_separation {c s t : ℝ} (ht : 0<t) {n : ℕ} (p : Equiv.Perm (Fin n)) :
    PaperAdmissible c s t p ↔ ∀ i j, i≠j → 2*t≤gaugeR c s (center p i-center p j) := by
  unfold PaperAdmissible Pairwise
  simp only [Function.onFun,separation_iff ht,add_sub_add_right_eq_sub]

lemma paperMin_iff {c s t : ℝ} (ht : 0<t) {n : ℕ} (p : Equiv.Perm (Fin n)) :
    PaperMin c s t p ↔ HexMin c s t p := by
  unfold PaperMin HexMin HexFits
  simp only [paper_separation ht]
  constructor
  · rintro ⟨hn,hp,hm⟩
    exact ⟨hn,hp,fun m ⟨hg,q,hq⟩ => hm m q hg hq⟩
  · rintro ⟨hn,hp,hm⟩
    exact ⟨hn,hp,fun m q hg hq => hm m ⟨hg,q,hq⟩⟩

theorem eventually_paper_min_exists {c s : ℝ} (hU : c^2+s^2=1) :
    ∀ᶠ t in atTop, ∃ (n : ℕ) (p : Equiv.Perm (Fin n)), PaperMin c s t p := by
  filter_upwards [eventually_min_exists hU,eventually_ge_atTop (1:ℝ)] with t ht h1
  obtain ⟨n,p,hp⟩ := ht
  exact ⟨n,p,(paperMin_iff (by linarith) _).mpr hp⟩

theorem regular_hexagon_limit {c s : ℝ} (hU : c^2+s^2=1)
    {n : ℝ→ℕ} (p : ∀ t, Equiv.Perm (Fin (n t)))
    (h : ∀ᶠ t in atTop, PaperMin c s t (p t)) :
    Tendsto (fun t => paperDensity c s t (p t)) atTop (𝓝 1) := by
  have hmin : ∀ᶠ t in atTop, HexMin c s t (p t) := by
    filter_upwards [h,eventually_ge_atTop (1:ℝ)] with t ht h1
    exact (paperMin_iff (by linarith) _).mp ht
  apply (oriented_hex_limit hU p hmin).congr'
  filter_upwards [h] with t ht
  exact (paperDensity_eq (le_trans (by decide : 1≤2) ht.1) c s t (p t)).symm

theorem singleton_degenerate (c s t : ℝ) :
    PaperAdmissible c s t (Equiv.refl (Fin 1)) ∧ volume (box 1 1) = 0 := by
  constructor
  · intro i j hne
    exact False.elim (hne (Subsingleton.elim i j))
  · rw [volume_box _ _ le_rfl]
    norm_num

#print axioms eventually_paper_min_exists
#print axioms regular_hexagon_limit
#print axioms singleton_degenerate
end PermHex
