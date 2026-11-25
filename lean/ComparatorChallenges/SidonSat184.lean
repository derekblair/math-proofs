import Mathlib

/-! # Saturated 9-element Sidon set in `[1, 184]` (SS-001) -/

namespace SidonSat184

def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

def IsSaturated (A : Finset ℕ) (N : ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ IsSidon A ∧
    ∀ x ∈ Finset.Icc 1 N, x ∉ A → ¬ IsSidon (insert x A)

def astar : Finset ℕ := {16, 62, 66, 74, 88, 104, 117, 122, 123}

theorem unique_extension_saturated {A : Finset ℕ} {N x : ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hx : x ∈ Finset.Icc 1 N)
    (hs : IsSidon (insert x A))
    (hunique : ∀ y ∈ Finset.Icc 1 N, y ∉ A → IsSidon (insert y A) → y = x) :
    IsSaturated (insert x A) N := by
  sorry

theorem r47_sat184 : astar.card = 9 ∧ IsSaturated astar 184 := by
  sorry

end SidonSat184
