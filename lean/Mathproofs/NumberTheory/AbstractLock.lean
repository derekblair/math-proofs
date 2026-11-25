/-
  AbstractLock.lean — R280/R287 abstract lock theory (repaired (a)/(b)/(c)): consecutive-firing characterization, gap-window repair, W={0,2} sharpness witness.

  Paper: papers/abstract-lock-transdag-October-11-2026/
  Status: [PROVED] — consecT_gives_consec_fire, no_consecT_scattered, consec_window_no_consecT_not_full, full_no_consecT_gap_window, sharpness_witness
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); R310: bakkie full-library build exit 0, zero sorrys, axioms standard-only.
-/

/-
  AbstractLock.lean — Lean formalization of R287's repaired Theorem 3(iii′)
  (the sharp repair of R280's T3(iii) after Q-24's W={0,2} objection).

  Source: ~/workspace/math-unsolved/ROUND287_DOSSIER.md (§2–§3).
  Rule-9 hostile review Q-32: quoted "Q-32: (a) SURVIVES, (b) SURVIVES,
  (c) SURVIVES for complete finite nonempty frames with integer adjacency.
  Clause (c) sharpness is a window-only guarantee uniformly over ε."
  (Bunny, #agents thread 1791707275.724949, 2026-10-11 ~01:29 PDT.)
  The rule-9 gate is OPEN for the repaired clauses (a)/(b)/(c).

  Setting: a complete abstract lock frame over window W (Finset ℤ) with edge
  predicate ε : ℤ → Bool. FIRE(L) = {t ∈ W : ε t = true} (R280 Theorem 2,
  cited as the definitional bridge — formalized here as `fire`). Full is
  defined as ε ≡ true on W (R280 Theorem 2(i)).

  Honesty labels:
  - consecT_gives_consec_fire, no_consecT_scattered (a): [PROVED*] hand
    proofs, Lean-checked below.
  - full_no_consecT_gap_window, consec_window_no_consecT_not_full (c)(i)(ii):
    [PROVED*] hand proofs, Lean-checked below.
  - sharpness_witness: Q-24's counterexample re-derived (W={0,2}, ε true
    exactly on W — full, no consecutive T's anywhere, W a gap window),
    showing (c)(i)'s consecutive-integer premise is necessary.
  - The 472-frame [COMPUTED]×2 sweep (r287_lock_repair_path1/2.py) is cited
    data, never re-claimed here.
  - The ORIGINAL T3(iii) "no-full-on-|W|≥2" clause stays FALSE (Q-24's
    objection stands) — it is NOT formalized here.
  - Q-17 (R271) / Q-21 (R276) verdicts still gate the abstract theory's
    concrete justification — noted, not duplicated.

  Lean 4.34.1 / Mathlib (pin d13f23b). Zero sorrys. Standard axioms only.
-/

import Mathlib

namespace AbstractLock

/-- The firing set of a complete frame: FIRE = {t ∈ W : ε t = true}
    (R280 Theorem 2, definitional bridge). -/
def fire (W : Finset ℤ) (ε : ℤ → Bool) : Finset ℤ :=
  W.filter (fun t => ε t = true)

/-- Membership unfolds definitionally. -/
theorem mem_fire {W : Finset ℤ} {ε : ℤ → Bool} {t : ℤ} :
    t ∈ fire W ε ↔ t ∈ W ∧ ε t = true := by
  simp [fire]

/-- R287 (a), forward: consecutive ε-true points in W give two consecutive
    integers in FIRE (a consecutive-firing lock). -/
theorem consecT_gives_consec_fire {W : Finset ℤ} {ε : ℤ → Bool} {n : ℤ}
    (hn : n ∈ W) (hn1 : n + 1 ∈ W)
    (e1 : ε n = true) (e2 : ε (n + 1) = true) :
    ∃ m, m ∈ fire W ε ∧ m + 1 ∈ fire W ε :=
  ⟨n, mem_fire.mpr ⟨hn, e1⟩, mem_fire.mpr ⟨hn1, e2⟩⟩

/-- R287 (a), contrapositive: if ε has no consecutive T's anywhere, then FIRE
    contains no two consecutive integers — firing is scattered. -/
theorem no_consecT_scattered {W : Finset ℤ} {ε : ℤ → Bool}
    (h : ∀ n : ℤ, ¬(ε n = true ∧ ε (n + 1) = true)) :
    ∀ m : ℤ, m ∈ fire W ε → m + 1 ∈ fire W ε → False := by
  intro m hm hm1
  rw [mem_fire] at hm hm1
  exact h m ⟨hm.2, hm1.2⟩

/-- R287 (c)(i): if W contains two consecutive integers and ε has no
    consecutive T's, the frame is NOT full. The consecutive-integer premise
    is NECESSARY (see `sharpness_witness`). -/
theorem consec_window_no_consecT_not_full {W : Finset ℤ} {ε : ℤ → Bool}
    {n : ℤ} (hn : n ∈ W) (hn1 : n + 1 ∈ W)
    (h : ∀ k : ℤ, ¬(ε k = true ∧ ε (k + 1) = true)) :
    ¬ (∀ t ∈ W, ε t = true) := by
  intro hfull
  exact h n ⟨hfull n hn, hfull (n + 1) hn1⟩

/-- R287 (c)(ii), equivalent form: full ∧ (ε has no consecutive T's) ⟹ W is a
    gap window (contains no two consecutive integers). -/
theorem full_no_consecT_gap_window {W : Finset ℤ} {ε : ℤ → Bool}
    (hfull : ∀ t ∈ W, ε t = true)
    (h : ∀ k : ℤ, ¬(ε k = true ∧ ε (k + 1) = true)) :
    ∀ n : ℤ, n ∈ W → n + 1 ∈ W → False := by
  intro n hn hn1
  exact h n ⟨hfull n hn, hfull (n + 1) hn1⟩

/-- Sharpness witness (Q-24's counterexample, re-derived): W={0,2} with ε true
    exactly on W is FULL, ε has no consecutive T's anywhere, and W contains
    no consecutive integers — so (c)(i)'s consecutive-integer premise cannot
    be dropped, and the original "no-full-on-|W|≥2" clause is false. -/
theorem sharpness_witness :
    (∀ t ∈ ({0, 2} : Finset ℤ), decide (t = 0 ∨ t = 2) = true) ∧
    (∀ k : ℤ, ¬(decide (k = 0 ∨ k = 2) = true ∧
                decide (k + 1 = 0 ∨ k + 1 = 2) = true)) ∧
    ¬∃ n : ℤ, n ∈ ({0, 2} : Finset ℤ) ∧ n + 1 ∈ ({0, 2} : Finset ℤ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rw [decide_eq_true_eq]
    rcases ht with rfl | rfl <;> simp
  · intro k hk
    have hk1 : k = 0 ∨ k = 2 := of_decide_eq_true hk.1
    have hk2 : k + 1 = 0 ∨ k + 1 = 2 := of_decide_eq_true hk.2
    omega
  · rintro ⟨n, hn, hn1⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn hn1
    omega
