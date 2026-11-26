import BK73Core
import Mathlib.Data.Nat.Bits
import Mathlib.Data.List.Basic

namespace BK73

theorem testBit_ofBits (l : List Bool) (k : Nat) : (ofBits l).testBit k = l.getD k false := by
  induction l generalizing k with
  | nil => simp [ofBits]
  | cons b l ih =>
    cases k with
    | zero => simp [ofBits, Nat.testBit_bit_zero]
    | succ k => simp [ofBits, Nat.testBit_bit_succ, ih]

theorem allL_succ (p : List Bool → Bool) (n z : Nat) (acc : List Bool) :
    allL p (n+1) z acc = (allL p n z (true :: acc) &&
      Nat.rec (motive := fun _ => Bool) true (fun z' _ => allL p n z' (false :: acc)) z) := rfl

theorem allL_zero (p : List Bool → Bool) (z : Nat) (acc : List Bool) :
    allL p 0 z acc = p acc := rfl

theorem allL_sound (p : List Bool → Bool) :
    ∀ n z acc, allL p n z acc = true →
      ∀ l : List Bool, l.length = n → l.count false ≤ z → p (l.reverse ++ acc) = true := by
  intro n
  induction n with
  | zero =>
    intro z acc h l hl _
    have : l = [] := List.length_eq_zero_iff.mp hl
    subst this; simpa [allL_zero] using h
  | succ n ih =>
    intro z acc h l hl hz
    rw [allL_succ, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    match l, hl, hz with
    | true :: l', hl, hz =>
      have := ih z (true :: acc) h1 l' (by simpa using hl) (by simpa using hz)
      simpa [List.reverse_cons, List.append_assoc] using this
    | false :: l', hl, hz =>
      cases z with
      | zero => simp at hz
      | succ z' =>
        have h2' : allL p n z' (false :: acc) = true := h2
        have := ih z' (false :: acc) h2' l' (by simpa using hl) (by simpa using hz)
        simpa [List.reverse_cons, List.append_assoc] using this

/-- split helper used to assemble the kernel chunks -/
theorem allL_split (p : List Bool → Bool) (n z : Nat) (acc : List Bool)
    (h1 : allL p n z (true :: acc) = true)
    (h2 : ∀ z', z = z' + 1 → allL p n z' (false :: acc) = true) :
    allL p (n+1) z acc = true := by
  rw [allL_succ, Bool.and_eq_true]
  refine ⟨h1, ?_⟩
  cases z with
  | zero => rfl
  | succ z' => exact h2 z' rfl

end BK73
