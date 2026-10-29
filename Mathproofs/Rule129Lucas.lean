import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Prime.Defs

/-!
# Central binomial parity modulo two

The positive even case follows from Pascal's identity and symmetry. Lucas's
one-digit recurrence reduces the odd case to half its index; strong induction
then characterizes the indices with odd central binomial coefficient.
-/

namespace Mathproofs.Rule129Lucas

/-- L5: a positive even row has an even central binomial coefficient. -/
theorem centralBinomParity_even_pos (k : Nat) :
    Nat.choose (2 * (k + 1)) (k + 1) % 2 = 0 := by
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
    Nat.choose_succ_succ', Nat.choose_symm_half]
  simp [← two_mul]

/-- L6: Lucas's recurrence for the central coefficient of an odd row. -/
theorem centralBinomParity_odd (k : Nat) :
    Nat.choose (2 * k + 1) k % 2 = Nat.choose k (k / 2) % 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n := 2 * k + 1) (k := k) (p := 2)
  have hmod : (2 * k + 1) % 2 = 1 := by omega
  have hdiv : (2 * k + 1) / 2 = k := by omega
  have hchoose : Nat.choose 1 (k % 2) = 1 := by
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk <;> simp [hk]
  change Nat.choose (2 * k + 1) k % 2 =
    (Nat.choose ((2 * k + 1) % 2) (k % 2) *
      Nat.choose ((2 * k + 1) / 2) (k / 2)) % 2 at h
  rw [hmod, hdiv, hchoose, one_mul] at h
  exact h

/-- L7: the central binomial coefficient is odd exactly at Mersenne indices. -/
theorem centralBinom_mod_two_eq_one_iff (n : Nat) :
    Nat.choose n (n / 2) % 2 = 1 ↔ ∃ m : Nat, n = 2 ^ m - 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      exact ⟨fun _ => ⟨0, rfl⟩, fun _ => rfl⟩
    rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * (k + 1) :=
        ⟨n / 2 - 1, by omega⟩
      rw [show 2 * (k + 1) / 2 = k + 1 by omega,
        centralBinomParity_even_pos]
      constructor
      · intro h
        omega
      · rintro ⟨m, hm⟩
        cases m with
        | zero =>
          simp only [pow_zero, Nat.sub_self] at hm
          omega
        | succ m =>
          rw [pow_succ'] at hm
          have hp : 1 ≤ 2 ^ m := Nat.one_le_two_pow
          omega
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 :=
        ⟨n / 2, by omega⟩
      rw [show (2 * k + 1) / 2 = k by omega,
        centralBinomParity_odd, ih k (by omega)]
      constructor
      · rintro ⟨m, hm⟩
        refine ⟨m + 1, ?_⟩
        rw [pow_succ']
        have hp : 1 ≤ 2 ^ m := Nat.one_le_two_pow
        omega
      · rintro ⟨m, hm⟩
        cases m with
        | zero =>
          simp only [pow_zero, Nat.sub_self] at hm
          omega
        | succ m =>
          refine ⟨m, ?_⟩
          rw [pow_succ'] at hm
          have hp : 1 ≤ 2 ^ m := Nat.one_le_two_pow
          omega

end Mathproofs.Rule129Lucas
