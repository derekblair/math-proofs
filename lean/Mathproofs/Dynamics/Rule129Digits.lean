import Mathlib.Data.Nat.Digits.Defs

/-!
Binary digit spread and Mersenne numbers (M3).

The list fold lemmas (L11) and the all-ones characterization (L12) give the
zero-spread equivalence and its one-valued complement (L13), including `n = 0`.
-/

namespace Mathproofs.Rule129Digits

/-- A binary list containing `1` has maximum `1`. -/
theorem foldl_max_eq_one {d : Nat} {ds : List Nat}
    (h01 : ∀ x ∈ d :: ds, x ≤ 1) (h1 : 1 ∈ d :: ds) :
    ds.foldl max d = 1 := by
  induction ds generalizing d with
  | nil =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
    exact h1.symm
  | cons a ds ih =>
    change ds.foldl max (max d a) = 1
    apply ih
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact max_le (h01 d (by simp)) (h01 a (by simp))
      · exact h01 x (by simp [hx])
    · have hd := h01 d (by simp)
      have ha := h01 a (by simp)
      simp only [List.mem_cons] at h1 ⊢
      have hd' : d = 0 ∨ d = 1 := by omega
      have ha' : a = 0 ∨ a = 1 := by omega
      rcases hd' with rfl | rfl <;> rcases ha' with rfl | rfl <;> simp_all

/-- A nonempty binary list has minimum at most `1`, with equality exactly
when every entry is `1`. -/
theorem foldl_min_zero_one {d : Nat} {ds : List Nat}
    (h01 : ∀ x ∈ d :: ds, x ≤ 1) :
    ds.foldl min d ≤ 1 ∧
      (ds.foldl min d = 1 ↔ ∀ x ∈ d :: ds, x = 1) := by
  induction ds generalizing d with
  | nil => simpa using h01
  | cons a ds ih =>
    have hd := h01 d (by simp)
    have ha := h01 a (by simp)
    have h01' : ∀ x ∈ min d a :: ds, x ≤ 1 := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_trans (min_le_left d a) hd
      · exact h01 x (by simp [hx])
    obtain ⟨hle, hiff⟩ := ih h01'
    change ds.foldl min (min d a) ≤ 1 ∧
      (ds.foldl min (min d a) = 1 ↔ ∀ x ∈ d :: a :: ds, x = 1)
    refine ⟨hle, hiff.trans ?_⟩
    simp only [List.mem_cons, forall_eq_or_imp]
    have hd' : d = 0 ∨ d = 1 := by omega
    have ha' : a = 0 ∨ a = 1 := by omega
    rcases hd' with rfl | rfl <;> rcases ha' with rfl | rfl <;> simp
private theorem eq_replicate_length_of_forall_eq (L : List Nat) (a : Nat)
    (h : ∀ x ∈ L, x = a) : L = List.replicate L.length a := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
      rw [List.length_cons, List.replicate_succ]
      exact congrArg₂ List.cons (h x (by simp))
        (ih (by intro y hy; exact h y (by simp [hy])))

/-- A positive natural number has a one in its binary expansion. -/
theorem one_mem_digits_two {n : Nat} (hn : n ≠ 0) : 1 ∈ Nat.digits 2 n := by
  by_contra h
  have hz : ∀ x ∈ Nat.digits 2 n, x = 0 := by
    intro x hx
    have hb := Nat.digits_lt_base (by decide : 1 < 2) hx
    have hne : x ≠ 1 := by intro he; subst x; exact h hx
    omega
  apply hn
  calc
    n = Nat.ofDigits 2 (Nat.digits 2 n) := (Nat.ofDigits_digits 2 n).symm
    _ = Nat.ofDigits 2 (List.replicate (Nat.digits 2 n).length 0) :=
      congrArg (Nat.ofDigits 2) (eq_replicate_length_of_forall_eq _ 0 hz)
    _ = 0 := Nat.ofDigits_replicate_zero

/-- The value of a list of binary ones, with one added. -/
theorem ofDigits_two_replicate_one (m : Nat) :
    Nat.ofDigits 2 (List.replicate m 1) + 1 = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [List.replicate_succ, Nat.ofDigits_cons, pow_succ']
      omega

/-- Mersenne numbers have exactly the indicated number of binary ones. -/
theorem digits_two_mersenne (m : Nat) :
    Nat.digits 2 (2 ^ m - 1) = List.replicate m 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hp : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      have hs : 2 ^ (m + 1) - 1 = 2 * (2 ^ m - 1) + 1 := by
        rw [pow_succ']
        omega
      rw [hs, Nat.digits_def' (by decide) (by omega)]
      have hm : (2 * (2 ^ m - 1) + 1) % 2 = 1 := by omega
      have hd : (2 * (2 ^ m - 1) + 1) / 2 = 2 ^ m - 1 := by omega
      rw [hm, hd, ih, List.replicate_succ]

/-- All binary digits are one exactly for the Mersenne numbers, including zero. -/
theorem forall_digits_two_eq_one_iff_mersenne (n : Nat) :
    (∀ x ∈ Nat.digits 2 n, x = 1) ↔ ∃ m : Nat, n = 2 ^ m - 1 := by
  constructor
  · intro h
    refine ⟨(Nat.digits 2 n).length, ?_⟩
    have he := eq_replicate_length_of_forall_eq (Nat.digits 2 n) 1 h
    have hv := ofDigits_two_replicate_one (Nat.digits 2 n).length
    rw [← he, Nat.ofDigits_digits] at hv
    omega
  · rintro ⟨m, rfl⟩
    rw [digits_two_mersenne]
    intro x hx
    exact (List.mem_replicate.mp hx).2

/-- The binary digit spread vanishes exactly at the Mersenne numbers. -/
theorem digits_two_max_sub_min_eq_zero_iff (n : Nat) :
    (match Nat.digits 2 n with
     | [] => 0
     | d :: ds => ds.foldl max d - ds.foldl min d) = 0 ↔ ∃ m : Nat, n = 2 ^ m - 1 := by
  cases hL : Nat.digits 2 n with
  | nil =>
      have hn : n = 0 := Nat.digits_eq_nil_iff_eq_zero.mp hL
      subst n
      exact iff_of_true rfl ⟨0, rfl⟩
  | cons d ds =>
      change ds.foldl max d - ds.foldl min d = 0 ↔ ∃ m : Nat, n = 2 ^ m - 1
      have hn : n ≠ 0 := by intro hn; subst n; simp at hL
      have h01 : ∀ x ∈ d :: ds, x ≤ 1 := by
        intro x hx
        have hb := Nat.digits_lt_base (by decide : 1 < 2) (show x ∈ Nat.digits 2 n by
          rwa [hL])
        omega
      have h1 : 1 ∈ d :: ds := by simpa [hL] using one_mem_digits_two hn
      have hmax := foldl_max_eq_one h01 h1
      obtain ⟨hle, hmin⟩ := foldl_min_zero_one h01
      rw [hmax, ← forall_digits_two_eq_one_iff_mersenne n, hL, ← hmin]
      omega

/-- The binary digit spread is always at most one. -/
theorem digits_two_max_sub_min_le_one (n : Nat) :
    (match Nat.digits 2 n with
     | [] => 0
     | d :: ds => ds.foldl max d - ds.foldl min d) ≤ 1 := by
  cases hL : Nat.digits 2 n with
  | nil => decide
  | cons d ds =>
      change ds.foldl max d - ds.foldl min d ≤ 1
      have hn : n ≠ 0 := by intro hn; subst n; simp at hL
      have h01 : ∀ x ∈ d :: ds, x ≤ 1 := by
        intro x hx
        have hb := Nat.digits_lt_base (by decide : 1 < 2) (show x ∈ Nat.digits 2 n by
          rwa [hL])
        omega
      have h1 : 1 ∈ d :: ds := by simpa [hL] using one_mem_digits_two hn
      rw [foldl_max_eq_one h01 h1]
      exact Nat.sub_le _ _

/-- At every non-Mersenne number, the binary digit spread is one. -/
theorem digits_two_max_sub_min_eq_one_of_not_mersenne (n : Nat)
    (h : ¬ ∃ m : Nat, n = 2 ^ m - 1) :
    (match Nat.digits 2 n with
     | [] => 0
     | d :: ds => ds.foldl max d - ds.foldl min d) = 1 := by
  have hbound := digits_two_max_sub_min_le_one n
  have hnonzero := mt (digits_two_max_sub_min_eq_zero_iff n).mp h
  omega

end Mathproofs.Rule129Digits

