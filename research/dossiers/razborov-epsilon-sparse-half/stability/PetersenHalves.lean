import PetersenCharts

open scoped BigOperators
namespace PetersenStability

noncomputable def total (w : V → ℝ) (c : C) : ℝ := ∑ v ∈ F c, w v
noncomputable def remainder (w : V → ℝ) (c : C) : ℝ :=
  1/2 - total w c - w (anchor c) - w (side c)/4
noncomputable def half (w : V → ℝ) (c : C) (v : V) : ℝ :=
  (if full c v then w v else 0) + (if split c v then remainder w c / 3 else 0) +
  (if v = anchor c then w v else 0) + (if v = side c then w v / 4 else 0)

theorem mass (w : V → ℝ) (c : C) : ∑ v, half w c v = 1/2 := by
  simp only [half, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ← Finset.sum_filter]
  change total w c + (∑ _v ∈ P c, remainder w c / 3) + w (anchor c) + w (side c)/4 = _
  simp [countP, remainder]
  ring

structure Balanced (w : V → ℝ) : Prop where
  nonneg : ∀ v, 0 ≤ w v
  mass : ∑ v, w v = 1
  low : ∀ v, v.val < 10 → (49/500 : ℝ) ≤ w v

private theorem boundMass (w : V → ℝ) (h : Balanced w) (v : V) :
    w v ≤ if v.val < 10 then 59/500 else 1/50 := by
  have aux (a : V) : (if a.val < 10 ∧ a ≠ v then (49/500 : ℝ) else 0) ≤
      (if a ≠ v then w a else 0) := by
    split_ifs with A B B
    · exact h.low a A.1
    · exact False.elim (B A.2)
    · exact h.nonneg a
    · exact le_rfl
  have H := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun a _ => aux a)
  have hcard : ∀ v : V, ((Finset.univ : Finset V).filter
      (fun a => a.val < 10 ∧ a ≠ v)).card = if v.val < 10 then 9 else 10 := by decide
  simp only [← Finset.sum_filter, Finset.sum_const, hcard, nsmul_eq_mul] at H
  have hu : ∑ a ∈ (Finset.univ.erase v), w a = 1 - w v := by
    have := Finset.sum_erase_add (s := Finset.univ) w (Finset.mem_univ v)
    rw [h.mass] at this
    linarith
  have he : Finset.univ.filter (fun a : V => a ≠ v) = Finset.univ.erase v := by
    ext a
    simp
  rw [he, hu] at H
  split_ifs at H ⊢ <;> norm_num at H ⊢ <;> linarith

theorem total_bounds (w : V → ℝ) (h : Balanced w) (c : C) :
    147/500 ≤ total w c ∧ total w c ≤ 177/500 := by
  have has : ∀ c : C, ∀ v : V, v ∈ F c → v.val < 10 := by decide
  have hl := Finset.sum_le_sum (s := F c) (fun v hv => h.low v (has c v hv))
  have hu := Finset.sum_le_sum (s := F c) (fun v hv => by
    simpa only [ite_eq_left (has c v hv)] using boundMass w h v)
  simp [countF] at hl hu
  unfold total
  constructor <;> linarith

private theorem extra_is_out : ∀ c : C, 10 ≤ (anchor c).val ∧ 10 ≤ (side c).val := by decide

theorem remaining (w : V → ℝ) (h : Balanced w) (c : C) :
    (3/25 : ℝ) ≤ remainder w c ∧ remainder w c ≤ 103/500 := by
  obtain ⟨hl,hu⟩ := total_bounds w h c
  have hA := boundMass w h (anchor c)
  have hB := boundMass w h (side c)
  simp only [ite_eq_right (Nat.not_lt.mpr (extra_is_out c).1)] at hA
  simp only [ite_eq_right (Nat.not_lt.mpr (extra_is_out c).2)] at hB
  unfold remainder
  constructor <;> linarith [h.nonneg (anchor c), h.nonneg (side c)]

private theorem masks : ∀ c : C, ∀ v : V,
    (full c v = true → split c v = false ∧ v ≠ anchor c ∧ v ≠ side c) ∧
    (split c v = true → full c v = false ∧ v ≠ anchor c ∧ v ≠ side c ∧ v.val < 10) ∧
    (v = anchor c → full c v = false ∧ split c v = false ∧ v ≠ side c) ∧
    (v = side c → full c v = false ∧ split c v = false ∧ v ≠ anchor c) := by decide

theorem half_full (w : V → ℝ) (c : C) (v : V) (hv : full c v = true) :
    half w c v = w v := by
  obtain ⟨hp,ha,hb⟩ := (masks c v).1 hv
  simp [half,hv,hp,ha,hb]

theorem half_split (w : V → ℝ) (c : C) (v : V) (hv : split c v = true) :
    half w c v = remainder w c / 3 := by
  obtain ⟨hf,ha,hb,_⟩ := (masks c v).2.1 hv
  simp [half,hf,hv,ha,hb]

theorem half_side (w : V → ℝ) (c : C) :
    half w c (side c) = w (side c)/4 := by
  obtain ⟨hf,hp,hn⟩ := (masks c (side c)).2.2.2 rfl
  simp [half,hf,hp,hn]

theorem half_anchor (w : V → ℝ) (c : C) :
    half w c (anchor c) = w (anchor c) := by
  obtain ⟨hf,hp,hn⟩ := (masks c (anchor c)).2.2.1 rfl
  simp [half,hf,hp,hn]

theorem half_zero (w : V → ℝ) (c : C) (v : V) (hv : support c v = false) :
    half w c v = 0 := by
  simp [support, Bool.or_eq_false_iff] at hv
  simp [half,hv.1.1.1,hv.1.1.2,hv.1.2,hv.2]

theorem admissible (w : V → ℝ) (h : Balanced w) (c : C) (v : V) :
    0 ≤ half w c v ∧ half w c v ≤ w v := by
  obtain ⟨L,U⟩ := remaining w h c
  by_cases hf : full c v = true
  · rw [half_full _ _ _ hf]
    exact ⟨h.nonneg v, le_rfl⟩
  by_cases hp : split c v = true
  · rw [half_split _ _ _ hp]
    have hl := ((masks c v).2.1 hp).2.2.2
    constructor <;> linarith [h.low v hl]
  by_cases ha : v = anchor c
  · subst v
    rw [half_anchor]
    exact ⟨h.nonneg _, le_rfl⟩
  by_cases hb : v = side c
  · subst v
    rw [half_side]
    constructor <;> linarith [h.nonneg (side c)]
  · simp [half,hf,hp,ha,hb,h.nonneg v]

theorem cover_product (w : V → ℝ) (h : Balanced w) (c : C) (a b : V)
    (hc : cover c a b = true) :
    w a * w b / 12 ≤ half w c a * half w c b := by
  have L := (remaining w h c).1
  have hs (v : V) (hv : split c v = true) : w v ≤ remainder w c := by
    have hl := ((masks c v).2.1 hv).2.2.2
    have hb := boundMass w h v
    rw [ite_eq_left hl] at hb
    linarith
  simp only [cover, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
  rcases hc with ⟨ha,hb⟩ | ⟨ha,hb | hb⟩
  · rw [half_full _ _ _ ha, half_split _ _ _ hb]
    nlinarith [mul_nonneg (h.nonneg a) (sub_nonneg.mpr (hs b hb)),
      mul_nonneg (h.nonneg a) (h.nonneg b)]
  · rw [half_split _ _ _ ha, half_full _ _ _ hb]
    nlinarith [mul_nonneg (h.nonneg b) (sub_nonneg.mpr (hs a ha)),
      mul_nonneg (h.nonneg a) (h.nonneg b)]
  · subst b
    rw [half_split _ _ _ ha, half_side]
    nlinarith [mul_nonneg (h.nonneg (side c)) (sub_nonneg.mpr (hs a ha))]

theorem uniform (w : V → ℝ) (h : Balanced w) (a b : V) (he : edge a b = true) :
    (w a * w b)/80 ≤ (∑ c : C, half w c a * half w c b)/20 := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset C)) (fun c _ => show
      (if cover c a b then w a * w b / 12 else 0) ≤ half w c a * half w c b by
        split_ifs with hh
        · exact cover_product w h c a b hh
        · exact mul_nonneg (admissible w h c a).1 (admissible w h c b).1)
  simp only [← Finset.sum_filter, Finset.sum_const, countCover a b he, nsmul_eq_mul] at hsum
  split_ifs at hsum <;> norm_num at hsum <;>
    nlinarith [mul_nonneg (h.nonneg a) (h.nonneg b)]

#print axioms mass
#print axioms admissible
end PetersenStability
