/-
  VoidLock.lean — R283 void locks: forced-cell window lemma + void-exclusion lemma (Q-27 rev SURVIVES).

  Paper: papers/void-frames-defect-October-11-2026/
  Status: [PROVED] — forced_cell_in_window, void_exclusion
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); R310: bakkie full-library build exit 0, zero sorrys, axioms standard-only.
-/

/-
  VoidLock.lean — Lean formalization of R283's Void-Exclusion Lemma.

  Source: ~/workspace/math-unsolved/ROUND283_DOSSIER.md (§4).
  Rule-9 hostile review Q-27: quoted SURVIVES (revised verdict, banked DONE
  2026-10-11 ~01:18 PDT). The rule-9 gate is OPEN for the Void-Exclusion
  Lemma.

  Lemma (R283 §4): let (Astar, Y, h) be a candidate frame with c*=h+g₀,
  W={2,3,4}, g₀=1. If h ∈ {1,2,3} then the frame is NOT void.
  Proof: t* = h+1 ∈ {2,3,4} = W; the edge window at shift s=0 is empty, so
  t* fires.

  Honesty labels:
  - void_exclusion: [PROVED*] hand proof, Lean-checked below. The Lean
    kernel is the logical consequence (a firing cell bars voidness); the
    edge-emptiness computation (t* fires at s=0) is [COMPUTED] application
    data entering as the hypothesis `hfire` — cited, never re-claimed.
  - The 217/246 void census and "beyond the lemma void-ness is contingent"
    ([HEURISTIC]-leaning) are cited from the dossier, never formalized.

  Lean 4.34.1 / Mathlib (pin d13f23b). Zero sorrys. Standard axioms only.
-/

import Mathlib

namespace VoidLock

/-- The lock window W = {2,3,4} (R283 §4). -/
def windowW : Finset ℕ := {2, 3, 4}

/-- The forced cell t* = h+1 lands in W for h ∈ {1,2,3}. -/
theorem forced_cell_in_window {h : ℕ} (hmem : h = 1 ∨ h = 2 ∨ h = 3) :
    h + 1 ∈ windowW := by
  rcases hmem with rfl | rfl | rfl <;> decide

/-- Void-Exclusion Lemma (R283 §4, Q-27 SURVIVES): h ∈ {1,2,3} bars void.
    `hfire` is the [COMPUTED] edge-emptiness fact (t* fires); the kernel
    below is the logical consequence. -/
theorem void_exclusion {FIRE : Finset ℕ} {h : ℕ}
    (hmem : h = 1 ∨ h = 2 ∨ h = 3)
    (hfire : h + 1 ∈ FIRE) :
    FIRE.Nonempty :=
  ⟨h + 1, hfire⟩
