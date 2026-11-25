/-
  VoidUnion.lean — R283/R289 void frames under union forcing: tagged-set datum V1–V8 + k0=0 impossibility (Q-34 SURVIVES).

  Paper: papers/void-frames-defect-October-11-2026/
  Status: [PROVED] — V1_void_iff_zero … V8_forced_split, k0_zero_impossible
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); R310: bakkie full-library build exit 0, zero sorrys, axioms standard-only.
-/

/-
  VoidUnion.lean — Lean formalization of R289's void-union datum theorems
  V1–V8 and the k0=0 impossibility theorem.

  Source: ~/workspace/math-unsolved/ROUND289_DOSSIER.md (§1–§4).
  Rule-9 hostile review Q-34 (Bunny, #agents threads 1791706379.492009 and
  1791707275.724949, 2026-10-11 ~01:33/01:29 PDT), quoted:
  - "Q34 A: SURVIVES as the chosen tagged-set datum. B: V1–V8 SURVIVE with
    Q27's exclusion tags."
  - "Q34 C: k0=0 impossibility and flagship ES progression SURVIVE. ...
    this does NOT cover every k≡0 mod35. Full R7 acceptance remains
    source-unverified."
  - "Q34 D: all 30,381 void-frame pairs incl. self-pairs independently
    reproduce both distributions exactly. The 1,097/4,066 cell-0 census and
    original code independence remain UNVERIFIED. No blanket clearance."
  - "Q-34: scoped SURVIVES. A/B tagged-set statements, C k0=0 impossibility
    and flagship ES progression, D 30,381-pair reconstruction cleared.
    Original R289 implementation independence, cell-0 census and full R7
    acceptance remain unverified."
  The rule-9 gate is OPEN for: the tagged-set datum (A), V1–V8 with Q-27's
  exclusion tags (B), the k0=0 impossibility + flagship arithmetic skeleton
  (C). NOT cleared: the 1,097-quad cell-0 census as a Lean claim, code
  independence, "every k≡0 mod 35" coverage, full R7 acceptance — none of
  these are formalized here.

  Setting: frames as FIRE sets (Finset ℕ). For a pair (A, B): u = A ∪ B;
  the datum is (T, F, C) = (|u|, 0, |u|) — F ≡ 0 because pc ⟺ nonempty makes
  Pcov = u identically (the tagged-set choice, Q-34 A), and m ≡ 0 because
  W ∩ Hard6 = ∅ (V5, definitional here).

  Honesty labels:
  - V1–V8: [PROVED*] hand proofs (R289 §2), Lean-checked below. V8's forced
    cells use Q-27's exclusion tags as hypotheses.
  - k0_zero_impossible: [PROVED*] hand proof (R289 §4), Lean-checked below
    (pure arithmetic: ab ∣ ch with a+b=(4c−1)h forces ab ≤ ch < ab).
  - surgical_cell0_witness: the flagship (5,553,70,2,910,2765) arithmetic
    skeleton by decide; the R7/R281 predicates (prime-covering, covered,
    ES identity) enter as hypotheses — full R7 acceptance is
    source-unverified per Q-34, so it is cited, never claimed.
  - The 30,381-pair census and 1,097-quad census are cited [COMPUTED]×2
    data, never re-claimed here.

  Lean 4.34.1 / Mathlib (pin d13f23b). Zero sorrys. Standard axioms only.
-/

import Mathlib

namespace VoidUnion

/-- The void-union (T,F,C) datum of a frame pair (Q-34 A: the chosen
    tagged-set datum). F ≡ 0 definitionally (V4); m ≡ 0 since W ∩ Hard6 = ∅
    (V5, folded into the datum). -/
def datum (A B : Finset ℕ) : ℕ × ℕ × ℕ :=
  ((A ∪ B).card, 0, (A ∪ B).card)

/-- V1: void ⟺ zero triple. -/
theorem V1_void_iff_zero (A : Finset ℕ) :
    A = ∅ ↔ datum A A = (0, 0, 0) := by
  constructor
  · intro h
    simp [datum, h]
  · intro h
    simp only [datum, Prod.mk.injEq] at h
    obtain ⟨h1, -, -⟩ := h
    have h2 : A ∪ A = ∅ := Finset.card_eq_zero.mp h1
    have h3 : A ⊆ A ∪ A := Finset.subset_union_left
    rw [h2] at h3
    exact Finset.subset_empty.mp h3

/-- V2: voids are the union-identity — datum(void ∪ L) = datum(L). -/
theorem V2_void_identity (B : Finset ℕ) :
    datum ∅ B = datum B B := by
  simp [datum]

/-- V3: void ∪ void is void. -/
theorem V3_void_stable : datum (∅ : Finset ℕ) ∅ = (0, 0, 0) := by
  simp [datum]

/-- V4: F ≡ 0 on all frame unions (no bottleneck component). -/
theorem V4_F_vanishes (A B : Finset ℕ) : (datum A B).2.1 = 0 := rfl

/-- V5: C = T = |u| (pure contingency, no hard-cell content). -/
theorem V5_pure_contingent (A B : Finset ℕ) :
    (datum A B).2.2 = (datum A B).1 ∧ (datum A B).1 = (A ∪ B).card :=
  ⟨rfl, rfl⟩

/-- V6: T is subadditive under union. -/
theorem V6_subadd (A B : Finset ℕ) :
    (datum A B).1 ≤ (datum A A).1 + (datum B B).1 := by
  show (A ∪ B).card ≤ (A ∪ A).card + (B ∪ B).card
  calc (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le A B
    _ ≤ (A ∪ A).card + (B ∪ B).card := by
        have e1 : A.card ≤ (A ∪ A).card :=
          Finset.card_le_card Finset.subset_union_left
        have e2 : B.card ≤ (B ∪ B).card :=
          Finset.card_le_card Finset.subset_union_left
        omega

/-- V7: the chain T = F + C (R285's U1 identity survives the cross). -/
theorem V7_chain (A B : Finset ℕ) :
    (datum A B).1 = (datum A B).2.1 + (datum A B).2.2 := by
  simp [datum]

/-- V8: forced/contingent split of C. `forced` tags the Q-27 exclusion cells;
    the structural content is forced(L) ⊆ FIRE(L) (hypothesis, from Q-27's
    lemma) and union-distributivity of the tags. -/
theorem V8_forced_split (A B : Finset ℕ) (forced : Finset ℕ → Finset ℕ)
    (hforced_sub : ∀ L, forced L ⊆ L)
    (hforced_union : forced (A ∪ B) = forced A ∪ forced B) :
    (forced (A ∪ B)).card + ((A ∪ B) \ forced (A ∪ B)).card
      = (datum A B).2.2 := by
  have hsub : forced (A ∪ B) ⊆ A ∪ B := hforced_sub _
  have h := Finset.card_sdiff_add_card_eq_card hsub
  simp [datum]
  linarith

/-- R289 §4, k0=0 impossibility [PROVED*]: no lane-N R7 family with
    a+b=(4c−1)h has k0=0 — in ANY bounds, structural. At k0=0 the
    class-wide divisibility gives ab ∣ ch, so ab ≤ ch; but
    ab ≥ a+b−1 = (4c−1)h−1 > ch for c,h ≥ 1. Contradiction. -/
theorem k0_zero_impossible {a b c h : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hh : 1 ≤ h)
    (hsum : a + b = (4 * c - 1) * h)
    (hdvd : a * b ∣ c * h) : False := by
  have ha' : (1:ℤ) ≤ (a:ℤ) := by exact_mod_cast ha
  have hb' : (1:ℤ) ≤ (b:ℤ) := by exact_mod_cast hb
  have hc' : (1:ℤ) ≤ (c:ℤ) := by exact_mod_cast hc
  have hh' : (1:ℤ) ≤ (h:ℤ) := by exact_mod_cast hh
  -- (i) ab ≤ ch
  have hpos : (0:ℤ) < (c:ℤ) * (h:ℤ) := mul_pos (by linarith) (by linarith)
  have hdvd' : (a:ℤ) * (b:ℤ) ∣ (c:ℤ) * (h:ℤ) := by
    have h0 : ((a * b : ℕ):ℤ) ∣ ((c * h : ℕ):ℤ) :=
      Int.natCast_dvd_natCast.mpr hdvd
    simpa [Nat.cast_mul] using h0
  have hab_le : (a:ℤ) * (b:ℤ) ≤ (c:ℤ) * (h:ℤ) := Int.le_of_dvd hpos hdvd'
  -- (ii) ab ≥ a + b − 1, from (a−1)(b−1) ≥ 0
  have hab_ge : (a:ℤ) + (b:ℤ) - 1 ≤ (a:ℤ) * (b:ℤ) := by
    nlinarith [mul_nonneg (show (0:ℤ) ≤ (a:ℤ) - 1 by linarith)
                          (show (0:ℤ) ≤ (b:ℤ) - 1 by linarith)]
  -- (iii) ch < a + b − 1, via hsum: (4c−1)h − 1 − ch = h(3c−1) − 1 ≥ 1
  have hsum' : (a:ℤ) + (b:ℤ) = (4 * (c:ℤ) - 1) * (h:ℤ) := by
    have h1 : (1:ℕ) ≤ 4 * c := by omega
    have e : (((4 * c - 1) * h : ℕ):ℤ) = (4 * (c:ℤ) - 1) * (h:ℤ) := by
      rw [Nat.cast_mul, Nat.cast_sub h1]; push_cast; ring
    have e2 : (((a + b : ℕ)):ℤ) = (a:ℤ) + (b:ℤ) := by push_cast; ring
    rw [← e2, hsum, e]
  have hgt : (c:ℤ) * (h:ℤ) < (a:ℤ) + (b:ℤ) - 1 := by
    rw [hsum']
    nlinarith [mul_nonneg (show (0:ℤ) ≤ 3 * (c:ℤ) - 2 by linarith)
                          (show (0:ℤ) ≤ (h:ℤ) - 1 by linarith)]
  linarith

/-- Flagship arithmetic skeleton (R289 §4): the concrete checks for
    (a,b,c,h,k0,mprime) = (5,553,70,2,910,2765). The R7/R281 predicates
    (prime-covering, covered={0}, ES identity) enter as hypotheses — full
    R7 acceptance is source-unverified per Q-34, so it is cited, never
    claimed here. -/
theorem surgical_cell0_witness
    (is_prime_covering : Prop) (covered_zero : Prop) (es_identity : Prop)
    (hpc : is_prime_covering) (hcov : covered_zero) (hes : es_identity) :
    5 + 553 = (4 * 70 - 1) * 2 ∧ 35 ∣ 2765 ∧ 910 % 35 = 0 ∧ 910 < 2765 :=
  ⟨by decide, by decide, by decide, by decide⟩
