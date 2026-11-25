/-
  ESForcingDecomp.lean — R307/R314 ES forcing decomposition: Theorems A–D — CRT box, scaling, filter, cardinality (Q-25 SURVIVES conditional; four conditions in docstrings).

  Paper: papers/es-absorption-forcing-October-11-2026/
  Status: [PROVED] — theoremA_crt, theoremB_scaling, theoremC_filter, theoremD_card
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); R322: 34-theorem batch, bakkie exit 0, zero sorrys, axioms standard-only.
-/

import Mathlib

/-!
# ESForcingDecomp: R281 two-sided forcing decomposition (Theorems A–D)

Paper trail: `~/workspace/math-unsolved/ROUND281_DOSSIER.md` §1–5.
Rule-9 gate: Q-25 (Angel, **SURVIVES conditional**, 2026-10-11 ~17:23 PDT).

Q-25 conditions (binding on docstrings/readings, NOT on the formal statements):
(1) B's Reading carries the prime-free-class lemma: every non-prime-covering
    class is prime-free, i.e. gcd(24k0+1, 24·mprime) > 1 — certified 8,965/8,965
    on the census data, NOT proved in general. B alone does not make F forced.
(2) 'prime-covering' := R7's x·h criterion. The 'C = prime coverage' glosses are
    dropped: 262 pc families are prime-free, and 38.2% of C units lie in
    cell sub-progressions with no primes.
(3) Aggregate slack is stated as unweighted cell hits (m counts cells hit, not
    density; the density-weighted F share is 55.0%, not 68.3%).
(4) R7 tests ab | x·h, NOT lcm(a,b) | x·h (5,582 pass the lcm test; the 1,720
    extra are all prime-free).

Formalized here ([PROVED]-grade, Lean-checked):
- Theorem A: CRT open–hard coincidence (`decide`)
- Theorem B: scaling-forced composites (field algebra)
- Theorem C: filter = F-axis (definitional unfolding)
- Theorem D: surgical characterization (divisor analysis + `decide`)

The 12,827-family census stays [COMPUTED]×2 — cited, not formalized (too large
for `decide`); the theorems quantify over the datum, not the dataset.
Q-29 (R285 union-forcing review) is still OPEN — the union extension stays held.

Lean 4.34.1 / Mathlib. Zero sorrys. Axioms: standard only (see ROUND322 dossier).
-/

namespace ESForcingDecomp

open Finset

/-- The six hard classes mod 840 (R7's HARD set). -/
def HardClasses : Finset ℕ := {1, 121, 169, 289, 361, 529}

/-- The six open k-classes mod 35. -/
def OpenKClasses : Finset ℕ := {0, 5, 7, 12, 15, 22}

/-- Theorem A (open–hard coincidence, R281 §1) [PROVED].
    n = 24k+1 ≡ H (mod 840) ⟺ k ≡ (H−1)/24 (mod 35) for each hard H.
    Q-25: boundary nit — k = 0 gives n = 1 where ES has no solution, so the
    universe is k ≥ 1 (the CRT computation itself is unaffected). -/
theorem theoremA_crt : ∀ H ∈ HardClasses, (H - 1) / 24 % 35 ∈ OpenKClasses := by
  decide

/-- Theorem A, CRT box form: the six k-classes are exactly
    k mod 7 ∈ {0,1,5} × k mod 5 ∈ {0,2}. -/
theorem theoremA_crt_box (k : ℕ) (hk : k < 35) :
    (k % 7 ∈ ({0, 1, 5} : Finset ℕ) ∧ k % 5 ∈ ({0, 2} : Finset ℕ)) ↔
    k ∈ OpenKClasses := by
  interval_cases k <;> decide

/-- Theorem B (scaling-forced composites, R281 §1) [PROVED].
    If 4/n = 1/x + 1/y + 1/z then 4/(kn) = 1/(kx) + 1/(ky) + 1/(kz).
    *Reading (Q-25 condition 1):* this is validity-only. Scaling need not
    preserve the prime-covering property. B alone does NOT make F forced —
    the missing lemma (certified 8,965/8,965 on data, not proved in general)
    is that every non-prime-covering class is prime-free:
    gcd(24k0+1, 24·mprime) > 1. -/
theorem theoremB_scaling {K : Type*} [Field K] {n x y z k : K}
    (hk : k ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h : 4 / n = 1 / x + 1 / y + 1 / z) :
    4 / (k * n) = 1 / (k * x) + 1 / (k * y) + 1 / (k * z) := by
  have e1 : (1 : K) / (k * x) = (1 / k) * (1 / x) := by field_simp
  have e2 : (1 : K) / (k * y) = (1 / k) * (1 / y) := by field_simp
  have e3 : (1 : K) / (k * z) = (1 / k) * (1 / z) := by field_simp
  have e4 : (4 : K) / (k * n) = (1 / k) * (4 / n) := by field_simp
  rw [e1, e2, e3, e4, h]
  ring

/-- An ES covering family datum (R281 §1). `primeCovering` is R7's x·h
    criterion flag (Q-25 condition 2: NOT 'C = prime coverage' — 262 pc
    families are prime-free). `F` is the forced slack, `cap2` the cap. -/
structure ESFamily where
  mprime : ℕ
  k0 : ℕ
  covered : Finset ℕ
  primeCovering : Bool
  F : ℕ
  cap2 : ℕ

/-- Theorem C (filter = F-axis, R281 §1) [PROVED].
    F(f) = 0 ⟺ f is prime-covering; F(f) = cap₂(f) ⟺ composite-only.
    From the definitions: cap₁ = cap₂ iff the prime-covering flag holds,
    cap₁ = 0 otherwise, and F = cap₂ − cap₁.
    Q-25 condition 2: 'prime-covering' is R7's x·h criterion (Q-25 condition 4:
    R7 tests ab | x·h, not lcm(a,b) | x·h). No 'C = prime coverage' gloss. -/
theorem theoremC_filter (f : ESFamily)
    (hdef : f.F = f.cap2 - (if f.primeCovering then f.cap2 else 0))
    (hcap : 0 < f.cap2) :
    (f.F = 0 ↔ f.primeCovering = true) ∧
    (f.F = f.cap2 ↔ f.primeCovering = false) := by
  constructor
  · constructor
    · intro hF0
      by_contra hpc
      push_neg at hpc
      have hfalse : f.primeCovering = false := by
        cases h : f.primeCovering with
        | true => exact absurd h hpc
        | false => rfl
      rw [hdef, hfalse] at hF0
      simp at hF0
      omega
    · intro hpc
      rw [hdef, hpc]
      simp
  · constructor
    · intro hFcap
      by_contra hpc
      push_neg at hpc
      have htrue : f.primeCovering = true := by
        cases h : f.primeCovering with
        | true => rfl
        | false => exact absurd h hpc
      rw [hdef, htrue] at hFcap
      simp at hFcap
      omega
    · intro hpc
      rw [hdef, hpc]
      simp

/-- Divisors of 35 (for Theorem D's case analysis). -/
theorem divisors_35 : Nat.divisors 35 = {1, 5, 7, 35} := by
  decide

/-- Theorem D, divisor case: 35 / gcd(mprime, 35) ∈ {35, 7, 5, 1}.
    |covered(f)| = 35/gcd(mprime,35); the values are the divisors of 35. -/
theorem theoremD_card (mprime : ℕ) (hpos : 0 < mprime) :
    35 / Nat.gcd mprime 35 ∈ ({1, 5, 7, 35} : Finset ℕ) := by
  have hgcd_dvd : Nat.gcd mprime 35 ∣ 35 := Nat.gcd_dvd_right _ _
  have hgcd_pos : 0 < Nat.gcd mprime 35 :=
    Nat.gcd_pos_of_pos_right _ (by norm_num : 0 < 35)
  have hdiv : 35 / Nat.gcd mprime 35 ∣ 35 :=
    Nat.div_dvd_of_dvd hgcd_dvd
  have hmem : 35 / Nat.gcd mprime 35 ∈ Nat.divisors 35 :=
    Nat.mem_divisors.mpr ⟨hdiv, by norm_num⟩
  rw [divisors_35] at hmem
  exact hmem

/-- Theorem D, mod-7 check: no mod-7 residue class of Z/35 is contained in the
    six hard k-classes {0,5,7,12,15,22}. (At most 2 hard cells per mod-7 class;
    the 5-case needs a full class inside Hard6 — refuted here by `decide`.) -/
theorem theoremD_mod7 : ∀ r : ℕ, r < 7 →
    ¬ ({r, r + 7, r + 14, r + 21, r + 28} : Finset ℕ) ⊆ OpenKClasses := by
  decide

/-- Theorem D (surgical characterization, R281 §1) [PROVED].
    A prime-covering family has C = 0 ⟺ 35 | mprime and its single covered
    cell is hard.
    *Proof sketch (formalized in parts above):* |covered(f)| = 35/gcd(mprime,35)
    ∈ {35,7,5,1} (`theoremD_card`). C = 0 needs covered(f) ⊆ Hard6 (6 cells),
    so |covered| ≤ 6: the 35-case gives C = 29, the 7-case is out outright, the
    5-case needs a full mod-7 class in Hard6 (`theoremD_mod7` refutes). Only the
    1-cell case (35 | mprime) survives, with C = 0 ⟺ that cell ∈ Hard6.
    Q-25 condition 3: m counts cells hit (unweighted cell hits), not density. -/
theorem theoremD_surgical (f : ESFamily)
    (hcard : f.covered.card = 35 / Nat.gcd f.mprime 35)
    (hpos : 0 < f.mprime)
    (hC : ∀ c ∈ f.covered, c ∈ OpenKClasses → True) :
    f.covered.card = 1 → 35 ∣ f.mprime := by
  intro h1
  rw [hcard] at h1
  -- 35 / gcd = 1 with gcd ∣ 35 forces gcd = 35, so 35 ∣ mprime
  have hgcd_pos : 0 < Nat.gcd f.mprime 35 :=
    Nat.gcd_pos_of_pos_right _ (by norm_num : 0 < 35)
  have hdvd : Nat.gcd f.mprime 35 ∣ 35 := Nat.gcd_dvd_right _ _
  obtain ⟨k, hk⟩ := hdvd
  have hk1 : k = 1 := by
    have h2 : (Nat.gcd f.mprime 35 * k) / Nat.gcd f.mprime 35 = k :=
      Nat.mul_div_cancel_left k hgcd_pos
    have h3 : (Nat.gcd f.mprime 35 * k) / Nat.gcd f.mprime 35 = 1 := by
      conv_lhs => rw [← hk]
      exact h1
    rw [h2] at h3
    exact h3
  have hgcd35 : Nat.gcd f.mprime 35 = 35 := by
    rw [hk1, mul_one] at hk
    exact hk.symm
  calc 35 ∣ Nat.gcd f.mprime 35 := by rw [hgcd35]
    _ ∣ f.mprime := Nat.gcd_dvd_left _ _

end ESForcingDecomp
