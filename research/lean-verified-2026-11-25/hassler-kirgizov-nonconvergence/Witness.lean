import Window
import Mathlib.Tactic

namespace Emerging

/-- n must be at least 6; x ranges over 0 through n-5 inclusive. -/
def tall (n x i : Nat) : Nat :=
  match i with
  | 0 => x
  | 1 => n-4
  | 2 => n-2
  | 3 => n-1
  | 4 => n-3
  | _ => if n-i  ≤  x then n-i-1 else n-i

theorem tall0 (n x : Nat) : tall n x 0 = x := rfl

theorem tall_tail (n x i : Nat) (hi : 5  ≤  i) :
    tall n x i = if n-i  ≤  x then n-i-1 else n-i := by
  obtain ⟨k,rfl⟩ : ∃ k, i=k+5 := ⟨i-5,by omega⟩
  rfl

theorem tall_tail_properties (n x a b : Nat) (hx : x<n-4) (ha : 5 ≤ a)
    (hb : b<n) (hab : a<b) :
    tall n x a < n-4 ∧ tall n x b < n-4 ∧
    tall n x a ≠ x ∧ tall n x b ≠ x ∧ tall n x b < tall n x a := by
  rw [tall_tail n x a ha,tall_tail n x b (by omega)]
  split <;> split <;> omega

theorem tall_lt (n x i : Nat) (hn : 6  ≤  n) (hx : x<n-4) (hi : i<n) :
    tall n x i < n := by
  by_cases hh : 5  ≤  i
  · rw [tall_tail n x i hh]
    split <;> omega
  · have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases h with rfl|rfl|rfl|rfl|rfl <;> simp [tall] <;> omega

private theorem tall_inj_late (n x a b : Nat) (hx : x<n-4) (ha : a<n) (hb : b<n)
    (hba : a<b) (h5 : 5 ≤ b) : tall n x a ≠ tall n x b := by
  by_cases h6 : 5  ≤  a
  · exact Nat.ne_of_gt (tall_tail_properties n x a b hx h6 hb hba).2.2.2.2
  · have h : a=0 ∨ a=1 ∨ a=2 ∨ a=3 ∨ a=4 := by omega
    rw [tall_tail n x b h5]
    rcases h with rfl|rfl|rfl|rfl|rfl <;> simp [tall] <;> split <;> omega

theorem tall_inj (n x a b : Nat) (hn : 6  ≤  n) (hx : x<n-4) (ha : a<n) (hb : b<n)
    (he : tall n x a = tall n x b) : a=b := by
  rcases Nat.lt_trichotomy a b with h|h|h
  · exfalso
    by_cases h5 : 5 ≤ b
    · exact tall_inj_late n x a b hx ha hb h h5 he
    · have h1 : a=0 ∨ a=1 ∨ a=2 ∨ a=3 ∨ a=4 := by omega
      have h2 : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 := by omega
      rcases h1 with rfl|rfl|rfl|rfl|rfl <;>
        rcases h2 with rfl|rfl|rfl|rfl|rfl <;> simp [tall] at he <;> omega
  · exact h
  · exfalso
    by_cases h5 : 5 ≤ a
    · exact tall_inj_late n x b a hx hb ha h h5 he.symm
    · have h1 : a=0 ∨ a=1 ∨ a=2 ∨ a=3 ∨ a=4 := by omega
      have h2 : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 := by omega
      rcases h1 with rfl|rfl|rfl|rfl|rfl <;>
        rcases h2 with rfl|rfl|rfl|rfl|rfl <;> simp [tall] at he <;> omega

theorem tail_small (n x a : Nat) (hx : x<n-4) (ha : 5 ≤ a) (hb : a<n) :
  tall n x a < n-4 := by
  rw [tall_tail n x a ha]
  split <;> omega

theorem tall_desc (n x a b : Nat) (hx : x<n-4) (ha : 3 ≤ a) (hb : b<n) (hab : a<b) :
    tall n x b < tall n x a := by
  by_cases h5 : 5 ≤ a
  · exact (tall_tail_properties n x a b hx h5 hb hab).2.2.2.2
  · by_cases hh : 5 ≤ b
    · have hs := tail_small n x b hx hh hb
      have ha' : a=3 ∨ a=4 := by omega
      rcases ha' with rfl|rfl <;> change _ < _ <;> first | (change _ < n-1; omega) | (change _ < n-3; omega)
    · have ha' : a=3 := by omega
      have hb' : b=4 := by omega
      subst a b
      simp [tall]
      omega

theorem w4_cmp (r s : Fin 5) : w 4 r < w 4 s ↔ s.val < r.val := by decide +revert

theorem tall_word (n x i : Nat) (hx : x<n-4) (hn : 6 ≤ n) (hi : i+4<n) :
  ∃ j : Fin 7, matchWord (tall n x) i (w j) := by
  by_cases he : 3 ≤ i
  · refine ⟨4, ?_⟩
    intro r s
    rw [w4_cmp]
    constructor
    · intro h
      by_cases hc : s.val < r.val
      · exact hc
      · have hc' : r.val < s.val ∨ r.val = s.val := by omega
        rcases hc' with hh|hh
        · have hrev := tall_desc n x (i+r.val) (i+s.val) hx (by omega) (by have := s.isLt; omega) (by omega)
          omega
        · simp [hh] at h
    · intro h
      exact tall_desc n x (i+s.val) (i+r.val) hx (by omega) (by have := r.isLt; omega) (by omega)
  · have hh : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hh with rfl|rfl|rfl
    · refine ⟨1,?_⟩
      intro r s
      fin_cases r <;> fin_cases s <;> simp [w,tall] <;> omega
    · refine ⟨2,?_⟩
      intro r s
      have hsmall := tail_small n x 5 hx (by omega) (by omega)
      fin_cases r <;> fin_cases s <;> simp [w,tall] at * <;> split_ifs at * <;> omega
    · refine ⟨3,?_⟩
      intro r s
      obtain ⟨h5,h6,_,_,h56⟩ := tall_tail_properties n x 5 6 hx (by omega) (by omega) (by omega)
      fin_cases r <;> fin_cases s <;> simp [w,tall] at * <;> split_ifs at * <;> omega

end Emerging
