import Mathlib

/-! # CRT escape from local quadratic obstructions modulo 840 (ES-002) -/

theorem es_crt_escape {t : ℕ} (A B : Fin t → ℕ)
    (h8 : ∀ i, 8 ∣ A i)
    (hobstruction : ∀ i,
      (∃ q, q.Prime ∧ Odd q ∧ q ∣ A i ∧ ¬ IsSquare (B i : ZMod q)) ∨
        ¬ (B i ≡ 1 [MOD 8]))
    (r : ℕ) (hr : r = 1 ∨ r = 121 ∨ r = 169 ∨ r = 289 ∨ r = 361 ∨ r = 529) :
    Set.Infinite { p : ℕ | p.Prime ∧ p ≡ r [MOD 840] ∧
      ∀ i, ¬ (p ≡ B i [MOD (A i)]) } := by
  sorry
