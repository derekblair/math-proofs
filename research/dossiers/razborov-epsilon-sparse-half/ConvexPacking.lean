import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace SparseHalfConvexPacking

def IsConvex (g : ℝ → ℝ) (s : ℝ) : Prop :=
  ∀ x ∈ Set.Icc 0 s, ∀ y ∈ Set.Icc 0 s, ∀ u v : ℝ,
    0 ≤ u → 0 ≤ v → u+v=1 → g (u*x+v*y) ≤ u*g x+v*g y

theorem pair (g : ℝ → ℝ) (s x y : ℝ)
    (hc : IsConvex g s)
    (hx0 : 0 ≤ x) (hxs : x ≤ s) (hy0 : 0 ≤ y) (hys : y ≤ s) :
    g x + g y ≤ g (min s (x+y)) + g (max 0 (x+y-s)) := by
  let H := min s (x+y)
  let L := max 0 (x+y-s)
  have hs : L+H=x+y := by
    dsimp [L,H]
    by_cases h : x+y ≤ s
    · rw [min_eq_right h, max_eq_left (sub_nonpos.mpr h)]; ring
    · rw [min_eq_left (by linarith : s ≤ x+y),
        max_eq_right (by linarith : 0 ≤ x+y-s)]; ring
  have hHx : x ≤ H := le_min hxs (by linarith)
  have hHy : y ≤ H := le_min hys (by linarith)
  have hLx : L ≤ x := max_le hx0 (by linarith)
  have hLy : L ≤ y := max_le hy0 (by linarith)
  have hH : H ∈ Set.Icc 0 s := ⟨hx0.trans hHx, min_le_left ..⟩
  have hL : L ∈ Set.Icc 0 s := ⟨le_max_left .., hLx.trans hxs⟩
  by_cases he : H=L
  · have hx : x=L := by linarith
    have hy : y=L := by linarith
    change g x + g y ≤ g H + g L
    rw [hx, hy, he]
  · have hp : 0 < H-L := by
      have hh : L ≤ H := hLx.trans hHx
      rcases hh.lt_or_eq with h | h
      · linarith
      · exact False.elim (he h.symm)
    let u := (x-L)/(H-L)
    have hu : 0 ≤ u := div_nonneg (by linarith) hp.le
    have hu' : u ≤ 1 := (div_le_iff₀ hp).2 (by linarith)
    have hden : u*(H-L) = x-L := by
      dsimp [u]
      exact div_mul_cancel₀ _ hp.ne'
    have hx : u * H + (1-u) * L = x := by linarith [hden]
    have hy : (1-u) * H + u * L = y := by linarith [hden]
    have hx' := hc H hH L hL u (1-u) hu (show 0 ≤ 1-u by linarith) (show u+(1-u)=1 by ring)
    have hy' := hc H hH L hL (1-u) u (show 0 ≤ 1-u by linarith) hu (show (1-u)+u=1 by ring)
    rw [hx] at hx'
    rw [hy] at hy'
    change g x + g y ≤ g H + g L
    linarith

theorem pack (g : ℝ → ℝ) (s : ℝ) (hs : 0 ≤ s) (hg : g 0 = 0)
    (hc : IsConvex g s) (xs : List ℝ)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ s) :
    ∃ (k : ℕ) (r : ℝ), 0 ≤ r ∧ r ≤ s ∧ xs.sum = (k : ℝ)*s + r ∧
      (xs.map g).sum ≤ (k : ℝ)*g s + g r := by
  induction xs with
  | nil => exact ⟨0, 0, le_rfl, hs, by simp, by simp [hg]⟩
  | cons x xs ih =>
    obtain ⟨hx0,hxs'⟩ := hxs x (by simp)
    obtain ⟨k,r,hr0,hrs,ht,hw⟩ := ih (fun z hz => hxs z (by simp [hz]))
    have hb := pair g s x r hc hx0 hxs' hr0 hrs
    by_cases h : x+r ≤ s
    · rw [min_eq_right h, max_eq_left (sub_nonpos.mpr h), hg, add_zero] at hb
      exact ⟨k,x+r,by linarith,h,by simp only [List.sum_cons]; linarith,
        by simp only [List.map_cons,List.sum_cons]; linarith⟩
    · have h' : 0 ≤ x+r-s := by linarith
      rw [min_eq_left (by linarith : s ≤ x+r), max_eq_right h'] at hb
      refine ⟨k+1,x+r-s,h',by linarith,?_,?_⟩
      · simp only [List.sum_cons, Nat.cast_add, Nat.cast_one]
        linarith
      · simp only [List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one]
        linarith

#print axioms pack
end SparseHalfConvexPacking
