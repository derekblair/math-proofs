/-
  AbsorbedRegime.lean — R200 T5′ absorbed-regime theorems (m = 4c−1 arithmetic).

  Paper: papers/hole-suppression-absorption-October-11-2026/
  Status: [PROVED] — t5prime_R1/R2/R3/R6, t5prime_combined
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); R234: local + bakkie `lake build` exit 0, zero sorrys, axioms standard-only.
-/

/-
R200 — Absorbed 13|h regime: T5′ kernel (ROUND222, Lane 4).

Claims formalised (machine-checked; ROUND200_DOSSIER.md §2):
- T5′ [PROVED*]→[PROVED]: no non-dead quad with R ∈ {1,2,3,6}, in ANY regime.
  Machine-checked as the arithmetic kernel `t5prime_combined` plus the four
  case lemmas. The proof cites R200's hand-proof machinery (R180 Lemma 2,
  2/3-automaticity, the a≤2R/m bound chain) as premises — those stay cited,
  not re-derived. The machine-checked content is: under m = 4c−1, c ≥ 1, and
  m ≤ 2R, each of R ∈ {1,2,3,6} is impossible given the per-R automaticity
  conditions:
    R=1: m ≤ 2 contradicts m = 4c−1 ≥ 3.
    R=2: c even forces c ≥ 2, so m ≥ 7 > 4 ≥ m.
    R=3: 3|c forces c ≥ 3, so m ≥ 11 > 6 ≥ m.
    R=6: 2|c and 3|c force 6|c, so c ≥ 6 and m ≥ 23 > 12 ≥ m.
T2 (trichotomy extension), T3 (fiber-extruded slice), T4 (c≤320 self-bound),
and the 30-quad census stay [PROVED*]/[COMPUTED]; cited, not formalised.

Checked: Lean 4.34.1 + Mathlib v4.34.1, `lake build`, zero sorrys,
`#print axioms` standard-only.
-/
import Mathlib

namespace AbsorbedRegime

open Finset

/-- R200 §0: m = 4c−1 is always at least 3 (c ≥ 1). -/
theorem m_ge_three (m c : ℕ) (hc : 1 ≤ c) (hm : m = 4 * c - 1) : 3 ≤ m := by
  omega

/-- T5′ case R=1: m ≤ 2 contradicts m = 4c−1 ≥ 3. -/
theorem t5prime_R1 (m c : ℕ) (hc : 1 ≤ c) (hm : m = 4 * c - 1)
    (hbound : m ≤ 2) : False := by
  omega

/-- T5′ case R=2: c even forces c ≥ 2, so m ≥ 7 > 4 ≥ m. -/
theorem t5prime_R2 (m c : ℕ) (hc : 1 ≤ c) (heven : 2 ∣ c)
    (hm : m = 4 * c - 1) (hbound : m ≤ 4) : False := by
  omega

/-- T5′ case R=3: 3|c forces c ≥ 3, so m ≥ 11 > 6 ≥ m. -/
theorem t5prime_R3 (m c : ℕ) (hc : 1 ≤ c) (h3 : 3 ∣ c)
    (hm : m = 4 * c - 1) (hbound : m ≤ 6) : False := by
  omega

/-- T5′ case R=6: 2|c and 3|c force 6|c, so c ≥ 6 and m ≥ 23 > 12 ≥ m. -/
theorem t5prime_R6 (m c : ℕ) (hc : 1 ≤ c) (heven : 2 ∣ c) (h3 : 3 ∣ c)
    (hm : m = 4 * c - 1) (hbound : m ≤ 12) : False := by
  omega

/-- T5′ (R200): no non-dead quad with R ∈ {1,2,3,6}.
    Premises cited from the hand proof (R180 Lemma 2, 2/3-automaticity, the
    a ≤ 2R/m bound chain): m ≤ 2R, and the per-R automaticity conditions
    (c even at R ∈ {2,6}; 3|c at R ∈ {3,6}). -/
theorem t5prime_combined (m c R : ℕ) (hc : 1 ≤ c) (hm : m = 4 * c - 1)
    (hbound : m ≤ 2 * R)
    (hR : R = 1 ∨ R = 2 ∨ R = 3 ∨ R = 6)
    (haut2 : R = 2 → 2 ∣ c) (haut3 : R = 3 → 3 ∣ c)
    (haut6 : R = 6 → 2 ∣ c ∧ 3 ∣ c) : False := by
  rcases hR with rfl | rfl | rfl | rfl
  · exact t5prime_R1 m c hc hm (by omega : m ≤ 2)
  · exact t5prime_R2 m c hc (haut2 rfl) hm (by omega : m ≤ 4)
  · exact t5prime_R3 m c hc (haut3 rfl) hm (by omega : m ≤ 6)
  · obtain ⟨heven, h3⟩ := haut6 rfl
    exact t5prime_R6 m c hc heven h3 hm (by omega : m ≤ 12)

end AbsorbedRegime
