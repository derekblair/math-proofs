import Mathlib.Tactic
import Mathlib.Algebra.Field.Basic

/-
Round 7 identity — Erdős–Straus covering identity for n ≡ 217 (mod 264).

Source: ~/workspace/math-unsolved/ROUND7_DOSSIER.md
Preprint: ~/workspace/math-unsolved/preprints/erdos-straus-identity-217mod264.tex
(Theorem 1 there). The identity was discovered by exhaustive search over
12,827 candidate families in Mordell's splitting-lemma framework; it covers
1009, the smallest prime missed by the published Mordell/Yamamoto/Rosati
identities, and 1/11 of each of the six hard residue classes mod 840.

Checked with Lean 4.34.1 (leanprover/lean4:stable) + Mathlib.
-/

/-- The new Erdős–Straus covering identity: for n ≡ 217 (mod 264),
    4/n = 1/((n+3)/4) + 1/(n(n+3)) + 1/(n(n+3)/11), where the third term
    is the unit fraction 1/(n(n+3)/11) since 11 ∣ n(n+3). -/
theorem es_identity_217mod264 (n : ℕ) (h : n % 264 = 217) :
    (4 : ℚ) / (n : ℚ)
      = 1 / (((n : ℚ) + 3) / 4)
        + 1 / ((n : ℚ) * ((n : ℚ) + 3))
        + 1 / (((n : ℚ) * ((n : ℚ) + 3)) / 11) := by
  obtain ⟨k, hk⟩ : ∃ k, n = 264 * k + 217 := ⟨n / 264, by omega⟩
  have hn : 0 < n := by omega
  -- 4 ∣ (n+3): n+3 = 264k + 220 = 4(66k + 55)
  have h4dvd : (4 : ℕ) ∣ n + 3 := by omega
  -- 11 ∣ (n+3): n+3 = 264k + 220 = 11(24k + 20), since 217 + 3 = 220
  have h11dvd : (11 : ℕ) ∣ n + 3 := by omega
  obtain ⟨a, ha⟩ := h4dvd
  obtain ⟨b, hb⟩ := h11dvd
  have ha_pos : 0 < a := by omega
  have hb_pos : 0 < b := by omega
  have hN : (n : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hA : (a : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt ha_pos
  have hB : (b : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hb_pos
  have hN3 : (n : ℚ) + 3 = 4 * (a : ℚ) := by exact_mod_cast ha
  have hN3b : (n : ℚ) + 3 = 11 * (b : ℚ) := by exact_mod_cast hb
  have hN3_ne : (n : ℚ) + 3 ≠ 0 := by rw [hN3]; exact mul_ne_zero (by norm_num) hA
  have hNN3_ne : (n : ℚ) * ((n : ℚ) + 3) ≠ 0 := mul_ne_zero hN hN3_ne
  have hNB_ne : (n : ℚ) * (b : ℚ) ≠ 0 := mul_ne_zero hN hB
  have hNA_ne : (n : ℚ) * (a : ℚ) ≠ 0 := mul_ne_zero hN hA
  -- Denominator simplifications: (n+3)/4 = a and n(n+3)/11 = n*b
  have e1 : (((n : ℚ) + 3) / 4) = (a : ℚ) := by
    rw [hN3]; exact mul_div_cancel_left₀ _ (by norm_num)
  have e2 : ((n : ℚ) * ((n : ℚ) + 3)) / 11 = (n : ℚ) * (b : ℚ) := by
    rw [show (n : ℚ) * ((n : ℚ) + 3) = 11 * ((n : ℚ) * (b : ℚ)) by rw [hN3b]; ring]
    exact mul_div_cancel_left₀ _ (by norm_num)
  -- Key relation between the two witnesses: 11·(n·b) = n·(n+3)
  have h11 : (11 : ℚ) * ((n : ℚ) * (b : ℚ)) = (n : ℚ) * ((n : ℚ) + 3) := by
    rw [hN3b]; ring
  -- Step 1: 4/n - 1/a = 3/(n·a), using n+3 = 4a
  have key1 : (4 : ℚ) / (n : ℚ) - 1 / (a : ℚ) = 3 / ((n : ℚ) * (a : ℚ)) := by
    rw [div_sub_div _ _ hN hA,
      div_eq_div_iff (mul_ne_zero hN hA) (mul_ne_zero hN hA)]
    linear_combination -(↑n * ↑a) * hN3
  -- Step 2: 1/(n·b) = 11/(n·(n+3))
  have e4 : (1 : ℚ) / ((n : ℚ) * (b : ℚ)) = 11 / ((n : ℚ) * ((n : ℚ) + 3)) := by
    rw [div_eq_div_iff hNB_ne hNN3_ne]
    linear_combination -h11
  -- Step 3: combine the last two unit fractions
  have key2 : (1 : ℚ) / ((n : ℚ) * ((n : ℚ) + 3)) + 1 / ((n : ℚ) * (b : ℚ))
      = 12 / ((n : ℚ) * ((n : ℚ) + 3)) := by
    rw [e4, ← add_div]
    norm_num
  -- Step 4: 3/(n·a) = 12/(n·(n+3)), using n+3 = 4a
  have key3 : (3 : ℚ) / ((n : ℚ) * (a : ℚ)) = 12 / ((n : ℚ) * ((n : ℚ) + 3)) := by
    rw [div_eq_div_iff hNA_ne hNN3_ne]
    linear_combination 3 * (n : ℚ) * hN3
  rw [e1, e2]
  have h4n : (4 : ℚ) / (n : ℚ) = 1 / (a : ℚ) + 3 / ((n : ℚ) * (a : ℚ)) := by
    linarith [key1]
  rw [h4n, key3, ← key2]
  ring

/-- Worked example from the preprint: the identity at n = 1009,
    the smallest prime missed by all previously published identities.
    (n+3)/4 = 253, n(n+3) = 1021108, n(n+3)/11 = 92828. -/
example : (1 : ℚ) / 253 + 1 / 1021108 + 1 / 92828 = 4 / 1009 := by
  norm_num
