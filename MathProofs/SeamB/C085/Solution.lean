import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Seam B Entry C085 (OEIS A294912): Formal Refutation of Hilko Koning's Composite Characterization and Salvaged True Characterization

Formalizes all results pinned in `PIN-C085.md` v2
(`sha256: a40073c9a7a613f93535ebe7506920f188aba9ee31820696dbebd3072717d154`,
`Statement.lean sha256: dd7d31598cc866cc95105ea08face63cf668d71e5da8c24531b7f146785b2ae7`),
which supersedes `PIN-C085.md` v1 (`NO-GO`):

1. **Algebraic four-congruence reduction (`inA294912_odd_iff`, `c085_positive_characterization`)**:
   Proves purely over `ℕ` (without division modulo `n`) that for every `k > 1`,
   `inA294912 (2 * k + 1) ↔ (k % 2 = 1 ∧ (2 * k + 1) ∣ (2 ^ k + 1))`. This directly closes
   Koning's uncorrupted Dec 05 2019 / Jan 27 2022 `A244628` composite characterization
   (`c085_positive_characterization`).
2. **Exact dichotomy for Koning's factor-of-3 condition (`koning_backward`,
   `koning_iff_of_not_three_dvd`, `not_three_mul_dvd_of_three_dvd`, `koning_fails_iff`)**:
   Proves that for every `k > 1`:
   - `(3 * (2 * k + 1)) ∣ (2 ^ k + 1) → inA294912 (2 * k + 1)` unconditionally;
   - whenever `¬ (3 ∣ (2 * k + 1))`, Koning's biconditional holds unconditionally;
   - whenever `3 ∣ (2 * k + 1)`, `(3 * (2 * k + 1)) ∣ (2 ^ k + 1)` ALWAYS fails
     (via `2 ^ k + 1 ≡ 3 [MOD 9]` when `k % 6 = 1`), so a counterexample exists iff some
     multiple of `3` lies in `A294912`.
3. **Kernel-clean cyclotomic certificate and formal refutation (`c085_witness`, `c085_refutation`,
   `c085_witness_mod_3n`)**:
   At the smallest counterexample `k = 93,041,293,345`,
   `n = 2 * k + 1 = 186,082,586,691 = 3 * 131 * 281 * 617 * 2731`
   (`A244628(1138)` = `A376255(2)`, discovered in the scoping computation `SCOPING-C085.md` §4.3),
   proves `n ∣ (2 ^ k + 1)` by modular squaring on tiny `u_p ∈ {1, 65, 35, 77, 13}` and
   `Odd.nat_add_dvd_pow_add_pow` (never expanding `2 ^ 93041293345` or `2 ^ (n - 1)`),
   combining across pairwise coprime prime factors to prove `inA294912 186082586691`,
   while `not_three_mul_dvd_of_three_dvd` gives `¬ ((3 * 186082586691) ∣ (2 ^ 93041293345 + 1))`
   (and exact residue `2 * 186082586691 = 372,165,173,382`). Assembling this with
   `1 < 93041293345` and `¬Nat.Prime 186082586691` closes `c085_refutation`.
4. **Structural extensions (`inA294912_even_false`, `inA294912_one`, `inA294912_three`,
   `inA294912_mod_eight`, `c085_a244628_iff`, `c085_no_3p`, `c085_no_3p_sq`,
   `c085_first_positive_composite`)**:
   Proves even exclusion, guard sharpness at `k = 0, 1`, automatic upgrade `n ≡ 3 (mod 8)`
   via `ZMod.exists_sq_eq_neg_two_iff` (establishing exact identity with OEIS `A244628`),
   structural impossibility of `n = 3 * p` and `n = 3 * p ^ 2` counterexamples, and the
   non-vacuity witness `n = 476,971 = 11 * 131 * 331` (`k = 238,485`).
-/

namespace C085

/-- Defining four-congruence predicate of OEIS `A294912` on `n : ℕ` (Jonas Kaiser,
Nov 10 2017), with `ceiling((3/4)*n)` pinned to `(3 * n + 3) / 4` and `floor((1/4)*n)`
pinned to `n / 4` verbatim from `PIN-C085.md` v1/v2. -/
def inA294912 (n : ℕ) : Prop :=
  Nat.ModEq n (2 ^ (n - 1)) 1 ∧
  Nat.ModEq n ((2 * n - 1) * (2 ^ ((n - 1) / 2))) 1 ∧
  Nat.ModEq n (4 * ((3 * n + 3) / 4) - 2) 1 ∧
  Nat.ModEq n (2 ^ ((n + 1) / 2) + (n / 4) * 2 ^ (((n + 1) / 2) + 1)) 1

/-! ### Section 1: Pure `ℕ` algebraic reduction of the four congruences -/

/-- Step 1 (SCOPING §1.2): For every odd `n = 2 * k + 1`, Congruence 2 is equivalent to
`n ∣ (2 ^ k + 1)`. Proved purely in `ℕ` from `((2*n - 1)*2^k) + (2^k + 1) = n*(2*2^k) + 1`. -/
theorem c2_iff_dvd (k : ℕ) :
    Nat.ModEq (2 * k + 1) ((2 * (2 * k + 1) - 1) * (2 ^ ((2 * k + 1 - 1) / 2))) 1 ↔
      (2 * k + 1) ∣ (2 ^ k + 1) := by
  set n := 2 * k + 1
  have hdiv : (n - 1) / 2 = k := by omega
  rw [hdiv]
  have hsum : (2 * n - 1) * 2 ^ k + (2 ^ k + 1) = 1 + n * (2 * 2 ^ k) := by
    have hsub : 2 * n - 1 + 1 = 2 * n := by omega
    calc
      (2 * n - 1) * 2 ^ k + (2 ^ k + 1)
          = ((2 * n - 1) + 1) * 2 ^ k + 1 := by ring
      _ = (2 * n) * 2 ^ k + 1 := by rw [hsub]
      _ = 1 + n * (2 * 2 ^ k) := by ring
  have hsum_mod : Nat.ModEq n ((2 * n - 1) * 2 ^ k + (2 ^ k + 1)) 1 := by
    rw [hsum, Nat.ModEq, Nat.add_mul_mod_self_left]
  constructor
  · intro hc2
    have h1 : Nat.ModEq n (1 + (2 ^ k + 1)) (1 + 0) := by
      calc
        1 + (2 ^ k + 1) ≡ (2 * n - 1) * 2 ^ k + (2 ^ k + 1) [MOD n] := hc2.symm.add_right _
        _ ≡ 1 [MOD n] := hsum_mod
        _ = 1 + 0 := rfl
    exact Nat.dvd_of_mod_eq_zero (Nat.ModEq.add_left_cancel' 1 h1)
  · intro hdvd
    have h0 : Nat.ModEq n (2 ^ k + 1) 0 := Nat.modEq_zero_iff_dvd.mpr hdvd
    calc
      (2 * n - 1) * 2 ^ k = (2 * n - 1) * 2 ^ k + 0 := (Nat.add_zero _).symm
      _ ≡ (2 * n - 1) * 2 ^ k + (2 ^ k + 1) [MOD n] := h0.symm.add_left _
      _ ≡ 1 [MOD n] := hsum_mod

/-- Step 2 (SCOPING §1.2): For every `k > 1`, Congruence 3 holds at `n = 2 * k + 1` iff
`k % 2 = 1` (equivalently `n ≡ 3 [MOD 4]`). -/
theorem c3_iff_odd (k : ℕ) (hk : 1 < k) :
    Nat.ModEq (2 * k + 1) (4 * ((3 * (2 * k + 1) + 3) / 4) - 2) 1 ↔ k % 2 = 1 := by
  set n := 2 * k + 1
  rcases Nat.mod_two_eq_zero_or_one k with heven | hodd
  · constructor
    · intro hc3
      exfalso
      obtain ⟨m, hm⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
      have hm1 : 1 ≤ m := by omega
      have hceil : (3 * n + 3) / 4 = 3 * m + 1 := by omega
      have hlhs : 4 * ((3 * n + 3) / 4) - 2 = 4 * m + n * 2 := by omega
      rw [hlhs, Nat.ModEq, Nat.add_mul_mod_self_left] at hc3
      have hmod1 : (4 * m) % n = 4 * m := Nat.mod_eq_of_lt (by omega)
      have hmod2 : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
      rw [hmod1, hmod2] at hc3
      omega
    · intro h
      omega
  · constructor
    · intro _
      exact hodd
    · intro _
      obtain ⟨m, hm⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
      have hceil : (3 * n + 3) / 4 = 3 * m + 3 := by omega
      have hlhs : 4 * ((3 * n + 3) / 4) - 2 = 1 + n * 3 := by omega
      rw [hlhs, Nat.ModEq, Nat.add_mul_mod_self_left]

/-- Step 3 (SCOPING §1.2): `(2 * k + 1) ∣ (2 ^ k + 1)` implies Congruence 1
(`2 ^ (2 * k) ≡ 1 [MOD 2 * k + 1]`). -/
theorem c1_of_dvd (k : ℕ) (hdvd : (2 * k + 1) ∣ (2 ^ k + 1)) :
    Nat.ModEq (2 * k + 1) (2 ^ (2 * k + 1 - 1)) 1 := by
  set n := 2 * k + 1
  have hexp : n - 1 = 2 * k := by omega
  rw [hexp]
  have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hmul : (2 ^ k - 1) * (2 ^ k + 1) + 1 = 2 ^ (2 * k) := by
    have hsq : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by rw [two_mul, pow_add]
    rw [hsq]
    zify [hpos]
    ring
  have hdvd' : n ∣ (2 ^ k - 1) * (2 ^ k + 1) := dvd_mul_of_dvd_right hdvd (2 ^ k - 1)
  have h0 : Nat.ModEq n ((2 ^ k - 1) * (2 ^ k + 1)) 0 := Nat.modEq_zero_iff_dvd.mpr hdvd'
  rw [← hmul]
  simpa using h0.add_right 1

/-- Step 4 (SCOPING §1.2): For odd `k` (`n = 2 * k + 1 ≡ 3 [MOD 4]`), `n ∣ (2 ^ k + 1)`
implies Congruence 4, via the division-free `ℕ` identity
`2 ^ (k + 1) + (n / 4) * 2 ^ (k + 2) + (2 ^ k + 1) = 1 + n * 2 ^ k`. -/
theorem c4_of_odd_and_dvd (k : ℕ) (hodd : k % 2 = 1) (hdvd : (2 * k + 1) ∣ (2 ^ k + 1)) :
    Nat.ModEq (2 * k + 1)
      (2 ^ ((2 * k + 1 + 1) / 2) + ((2 * k + 1) / 4) * 2 ^ (((2 * k + 1 + 1) / 2) + 1)) 1 := by
  set n := 2 * k + 1
  obtain ⟨m, hm⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
  have h1 : (n + 1) / 2 = k + 1 := by omega
  have h2 : n / 4 = m := by omega
  rw [h1, h2]
  have hsum : 2 ^ (k + 1) + m * 2 ^ (k + 1 + 1) + (2 ^ k + 1) = 1 + n * 2 ^ k := by
    have h2m : 2 * m + 1 = k := hm.symm
    calc
      2 ^ (k + 1) + m * 2 ^ (k + 1 + 1) + (2 ^ k + 1)
          = (2 * (2 * m + 1) + 1) * 2 ^ k + 1 := by
              rw [pow_succ, pow_succ, pow_succ]
              ring
      _ = (2 * k + 1) * 2 ^ k + 1 := by rw [h2m]
      _ = 1 + n * 2 ^ k := by ring
  have hsum_mod : Nat.ModEq n (2 ^ (k + 1) + m * 2 ^ (k + 1 + 1) + (2 ^ k + 1)) 1 := by
    rw [hsum, Nat.ModEq, Nat.add_mul_mod_self_left]
  have h0 : Nat.ModEq n (2 ^ k + 1) 0 := Nat.modEq_zero_iff_dvd.mpr hdvd
  calc
    2 ^ (k + 1) + m * 2 ^ (k + 1 + 1)
        = 2 ^ (k + 1) + m * 2 ^ (k + 1 + 1) + 0 := (Nat.add_zero _).symm
    _ ≡ 2 ^ (k + 1) + m * 2 ^ (k + 1 + 1) + (2 ^ k + 1) [MOD n] := h0.symm.add_left _
    _ ≡ 1 [MOD n] := hsum_mod

/-- Step 5 (SCOPING §1.2): Complete collapse of the four-congruence predicate for ALL odd
`2 * k + 1 ≥ 5` (both prime and composite). -/
theorem inA294912_odd_iff (k : ℕ) (hk : 1 < k) :
    inA294912 (2 * k + 1) ↔ (k % 2 = 1 ∧ (2 * k + 1) ∣ (2 ^ k + 1)) := by
  constructor
  · rintro ⟨_, hc2, hc3, _⟩
    exact ⟨(c3_iff_odd k hk).mp hc3, (c2_iff_dvd k).mp hc2⟩
  · rintro ⟨hodd, hdvd⟩
    exact ⟨c1_of_dvd k hdvd, (c2_iff_dvd k).mpr hdvd,
      (c3_iff_odd k hk).mpr hodd, c4_of_odd_and_dvd k hodd hdvd⟩

/-- Salvaged true characterization of odd composites in `A294912` (Koning's uncorrupted
Dec 05 2019 / Jan 27 2022 `A244628` conjecture, omitting the spurious factor of `3`). -/
theorem c085_positive_characterization :
    ∀ k : ℕ, 1 < k → ¬Nat.Prime (2 * k + 1) →
      (inA294912 (2 * k + 1) ↔ (k % 2 = 1 ∧ (2 * k + 1) ∣ (2 ^ k + 1))) :=
  fun k hk _ => inA294912_odd_iff k hk

/-! ### Section 2: Exact dichotomy for Koning's `3 * (2 * k + 1)` divisibility condition -/

/-- `3 ∣ (2 ^ k + 1)` if and only if `k` is odd. -/
theorem three_dvd_two_pow_add_one_iff (k : ℕ) : 3 ∣ (2 ^ k + 1) ↔ k % 2 = 1 := by
  have h4 : Nat.ModEq 3 (2 ^ 2) 1 := by decide
  have h2q : ∀ q : ℕ, Nat.ModEq 3 (2 ^ (2 * q)) 1 := by
    intro q
    rw [pow_mul]
    simpa only [one_pow] using h4.pow q
  rcases Nat.mod_two_eq_zero_or_one k with heven | hodd
  · obtain ⟨q, rfl⟩ : ∃ q, k = 2 * q := ⟨k / 2, by omega⟩
    have hmod : Nat.ModEq 3 (2 ^ (2 * q) + 1) 2 := (h2q q).add_right 1
    constructor
    · intro hdvd
      have h0 : (2 ^ (2 * q) + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hdvd
      have h2 : (2 ^ (2 * q) + 1) % 3 = 2 := hmod
      omega
    · intro h
      omega
  · obtain ⟨q, rfl⟩ : ∃ q, k = 2 * q + 1 := ⟨k / 2, by omega⟩
    have hmod : Nat.ModEq 3 (2 ^ (2 * q + 1) + 1) 0 := by
      rw [pow_succ]
      have h1 : Nat.ModEq 3 (2 ^ (2 * q) * 2 + 1) (1 * 2 + 1) :=
        ((h2q q).mul_right 2).add_right 1
      exact h1.trans (by decide)
    exact ⟨fun _ => hodd, fun _ => Nat.dvd_of_mod_eq_zero hmod⟩

/-- Backward direction of Koning's biconditional holds unconditionally for all `k > 1`. -/
theorem koning_backward (k : ℕ) (hk : 1 < k) (h : (3 * (2 * k + 1)) ∣ (2 ^ k + 1)) :
    inA294912 (2 * k + 1) := by
  rw [inA294912_odd_iff k hk]
  have h3 : 3 ∣ (2 ^ k + 1) := dvd_trans (dvd_mul_right 3 (2 * k + 1)) h
  have hn : (2 * k + 1) ∣ (2 ^ k + 1) := dvd_trans (dvd_mul_left (2 * k + 1) 3) h
  exact ⟨(three_dvd_two_pow_add_one_iff k).mp h3, hn⟩

/-- Whenever `3 ∤ (2 * k + 1)`, Koning's biconditional holds unconditionally (covering all
primes `p > 3` and all 29 composites `< 25,000,000`). -/
theorem koning_iff_of_not_three_dvd (k : ℕ) (hk : 1 < k) (h3 : ¬ 3 ∣ (2 * k + 1)) :
    inA294912 (2 * k + 1) ↔ (3 * (2 * k + 1)) ∣ (2 ^ k + 1) := by
  constructor
  · intro hin
    rcases (inA294912_odd_iff k hk).mp hin with ⟨hodd, hdvd⟩
    have h3dvd : 3 ∣ (2 ^ k + 1) := (three_dvd_two_pow_add_one_iff k).mpr hodd
    have hcop : Nat.Coprime 3 (2 * k + 1) := (Nat.prime_three.coprime_iff_not_dvd).mpr h3
    exact hcop.mul_dvd_of_dvd_of_dvd h3dvd hdvd
  · exact koning_backward k hk

/-- Whenever `k ≡ 1 [MOD 6]`, `2 ^ k + 1 ≡ 3 [MOD 9]` (so `v_3(2 ^ k + 1) = 1`, `9 ∤ 2 ^ k + 1`). -/
theorem mod_nine_of_mod_six_eq_one (k : ℕ) (hk : k % 6 = 1) :
    Nat.ModEq 9 (2 ^ k + 1) 3 := by
  obtain ⟨q, rfl⟩ : ∃ q, k = 6 * q + 1 := ⟨k / 6, by omega⟩
  have h64 : Nat.ModEq 9 (2 ^ 6) 1 := by decide
  have h6q : Nat.ModEq 9 (2 ^ (6 * q)) 1 := by
    rw [pow_mul]
    simpa only [one_pow] using h64.pow q
  rw [pow_succ]
  simpa using ((h6q.mul_right 2).add_right 1)

/-- Whenever `3 ∣ (2 * k + 1)`, Koning's RHS `(3 * (2 * k + 1)) ∣ (2 ^ k + 1)` ALWAYS fails. -/
theorem not_three_mul_dvd_of_three_dvd (k : ℕ) (h3 : 3 ∣ (2 * k + 1)) :
    ¬ ((3 * (2 * k + 1)) ∣ (2 ^ k + 1)) := by
  intro hdvd
  rcases Nat.mod_two_eq_zero_or_one k with heven | hodd
  · have h3' : 3 ∣ (2 ^ k + 1) := dvd_trans (dvd_mul_right 3 (2 * k + 1)) hdvd
    have hodd' : k % 2 = 1 := (three_dvd_two_pow_add_one_iff k).mp h3'
    omega
  · have hk6 : k % 6 = 1 := by
      rcases h3 with ⟨t, ht⟩
      omega
    have h9 : 9 ∣ (3 * (2 * k + 1)) := by
      rcases h3 with ⟨t, ht⟩
      exact ⟨t, by omega⟩
    have h9dvd : 9 ∣ (2 ^ k + 1) := dvd_trans h9 hdvd
    have hrem0 : (2 ^ k + 1) % 9 = 0 := Nat.mod_eq_zero_of_dvd h9dvd
    have hrem3 : (2 ^ k + 1) % 9 = 3 := mod_nine_of_mod_six_eq_one k hk6
    omega

/-- Exact characterization of counterexamples to Koning's biconditional for `k > 1`:
the biconditional fails at `k` iff `2 * k + 1 ∈ A294912` and `3 ∣ (2 * k + 1)`. -/
theorem koning_fails_iff (k : ℕ) (hk : 1 < k) :
    ¬ (inA294912 (2 * k + 1) ↔ (3 * (2 * k + 1)) ∣ (2 ^ k + 1)) ↔
      (inA294912 (2 * k + 1) ∧ 3 ∣ (2 * k + 1)) := by
  constructor
  · intro hfail
    by_cases h3 : 3 ∣ (2 * k + 1)
    · refine ⟨?_, h3⟩
      by_contra hnot
      exact hfail ⟨fun h => absurd h hnot, fun h => absurd h (not_three_mul_dvd_of_three_dvd k h3)⟩
    · exact absurd (koning_iff_of_not_three_dvd k hk h3) hfail
  · rintro ⟨hin, h3⟩ hiff
    exact not_three_mul_dvd_of_three_dvd k h3 (hiff.mp hin)

/-! ### Section 3: Kernel-clean cyclotomic certificate, `c085_witness`, and `c085_refutation` -/

/-- Cyclotomic odd-quotient lifting lemma: if `p ∣ (2 ^ u + 1)` and `q` is odd,
then `p ∣ (2 ^ (u * q) + 1)` without ever expanding `2 ^ (u * q)`. -/
theorem dvd_two_pow_add_one_of_dvd_odd_quot (p u q : ℕ)
    (hu : p ∣ (2 ^ u + 1)) (hq : Odd q) : p ∣ (2 ^ (u * q) + 1) := by
  have hpow : 2 ^ (u * q) + 1 = (2 ^ u) ^ q + 1 ^ q := by rw [pow_mul, one_pow]
  rw [hpow]
  exact dvd_trans hu (hq.nat_add_dvd_pow_add_pow (2 ^ u) 1)

/-- `3 ∣ (2 ^ 1 + 1)` (certificate `u_3 = 1`). -/
private lemma dvd_3_base : 3 ∣ (2 ^ 1 + 1) := ⟨1, by norm_num⟩

/-- `2731 ∣ (2 ^ 13 + 1)` (certificate `u_2731 = 13`, `2 ^ 13 + 1 = 8193 = 2731 * 3`). -/
private lemma dvd_2731_base : 2731 ∣ (2 ^ 13 + 1) := ⟨3, by norm_num⟩

/-- `281 ∣ (2 ^ 35 + 1)` (certificate `u_281 = 35`), proved by small-modulus squaring. -/
private lemma dvd_281_base : 281 ∣ (2 ^ 35 + 1) := by
  have h8 : Nat.ModEq 281 (2 ^ 8) 256 := by norm_num [Nat.ModEq]
  have h16 : Nat.ModEq 281 (2 ^ 16) 63 := by
    have h1 : 2 ^ 16 = (2 ^ 8) ^ 2 := by rw [← pow_mul]
    rw [h1]
    exact (h8.pow 2).trans (by norm_num [Nat.ModEq])
  have h32 : Nat.ModEq 281 (2 ^ 32) 35 := by
    have h1 : 2 ^ 32 = (2 ^ 16) ^ 2 := by rw [← pow_mul]
    rw [h1]
    exact (h16.pow 2).trans (by norm_num [Nat.ModEq])
  have h35 : Nat.ModEq 281 (2 ^ 35) 280 := by
    have h1 : 2 ^ 35 = 2 ^ 32 * 2 ^ 3 := by rw [← pow_add]
    rw [h1]
    exact (h32.mul_right (2 ^ 3)).trans (by norm_num [Nat.ModEq])
  exact Nat.modEq_zero_iff_dvd.mp ((h35.add_right 1).trans (by norm_num [Nat.ModEq]))

/-- `131 ∣ (2 ^ 65 + 1)` (certificate `u_131 = 65`), proved by small-modulus squaring. -/
private lemma dvd_131_base : 131 ∣ (2 ^ 65 + 1) := by
  have h8 : Nat.ModEq 131 (2 ^ 8) 125 := by norm_num [Nat.ModEq]
  have h16 : Nat.ModEq 131 (2 ^ 16) 36 := by
    have h1 : 2 ^ 16 = (2 ^ 8) ^ 2 := by rw [← pow_mul]
    rw [h1]
    exact (h8.pow 2).trans (by norm_num [Nat.ModEq])
  have h32 : Nat.ModEq 131 (2 ^ 32) 117 := by
    have h1 : 2 ^ 32 = (2 ^ 16) ^ 2 := by rw [← pow_mul]
    rw [h1]
    exact (h16.pow 2).trans (by norm_num [Nat.ModEq])
  have h64 : Nat.ModEq 131 (2 ^ 64) 65 := by
    have h1 : 2 ^ 64 = (2 ^ 32) ^ 2 := by rw [← pow_mul]
    rw [h1]
    exact (h32.pow 2).trans (by norm_num [Nat.ModEq])
  have h65 : Nat.ModEq 131 (2 ^ 65) 130 := by
    have h1 : 2 ^ 65 = 2 ^ 64 * 2 := by rw [pow_succ]
    rw [h1]
    exact (h64.mul_right 2).trans (by norm_num [Nat.ModEq])
  exact Nat.modEq_zero_iff_dvd.mp ((h65.add_right 1).trans (by norm_num [Nat.ModEq]))

/-- `617 ∣ (2 ^ 77 + 1)` (certificate `u_617 = 77`), proved by small-modulus squaring. -/
private lemma dvd_617_base : 617 ∣ (2 ^ 77 + 1) := by
  have h8 : Nat.ModEq 617 (2 ^ 8) 256 := by norm_num [Nat.ModEq]
  have h16 : Nat.ModEq 617 (2 ^ 16) 134 := by
    have h1 : 2 ^ 16 = (2 ^ 8) ^ 2 := by rw [← pow_mul]
    rw [h1]
    exact (h8.pow 2).trans (by norm_num [Nat.ModEq])
  have h32 : Nat.ModEq 617 (2 ^ 32) 63 := by
    have h1 : 2 ^ 32 = (2 ^ 16) ^ 2 := by rw [← pow_mul]
    rw [h1]
    exact (h16.pow 2).trans (by norm_num [Nat.ModEq])
  have h64 : Nat.ModEq 617 (2 ^ 64) 267 := by
    have h1 : 2 ^ 64 = (2 ^ 32) ^ 2 := by rw [← pow_mul]
    rw [h1]
    exact (h32.pow 2).trans (by norm_num [Nat.ModEq])
  have h72 : Nat.ModEq 617 (2 ^ 72) 482 := by
    have h1 : 2 ^ 72 = 2 ^ 64 * 2 ^ 8 := by rw [← pow_add]
    rw [h1]
    exact (h64.mul h8).trans (by norm_num [Nat.ModEq])
  have h77 : Nat.ModEq 617 (2 ^ 77) 616 := by
    have h1 : 2 ^ 77 = 2 ^ 72 * 2 ^ 5 := by rw [← pow_add]
    rw [h1]
    exact (h72.mul_right (2 ^ 5)).trans (by norm_num [Nat.ModEq])
  exact Nat.modEq_zero_iff_dvd.mp ((h77.add_right 1).trans (by norm_num [Nat.ModEq]))

/-- Kernel-clean divisibility `186082586691 ∣ (2 ^ 93041293345 + 1)` obtained by combining the
five pairwise-coprime prime factors `3 * 131 * 281 * 617 * 2731` via the cyclotomic odd-quotient
certificate `u_p ∈ {1, 65, 35, 77, 13}`. -/
theorem witness_dvd : 186082586691 ∣ (2 ^ 93041293345 + 1) := by
  have hd3 : 3 ∣ (2 ^ 93041293345 + 1) := by
    have h := dvd_two_pow_add_one_of_dvd_odd_quot 3 1 93041293345 dvd_3_base ⟨46520646672, by norm_num⟩
    simpa only [one_mul] using h
  have hd131 : 131 ∣ (2 ^ 93041293345 + 1) := by
    have h := dvd_two_pow_add_one_of_dvd_odd_quot 131 65 1431404513 dvd_131_base
      ⟨715702256, by norm_num⟩
    have heq : 65 * 1431404513 = 93041293345 := by norm_num
    rwa [heq] at h
  have hd281 : 281 ∣ (2 ^ 93041293345 + 1) := by
    have h := dvd_two_pow_add_one_of_dvd_odd_quot 281 35 2658322667 dvd_281_base
      ⟨1329161333, by norm_num⟩
    have heq : 35 * 2658322667 = 93041293345 := by norm_num
    rwa [heq] at h
  have hd617 : 617 ∣ (2 ^ 93041293345 + 1) := by
    have h := dvd_two_pow_add_one_of_dvd_odd_quot 617 77 1208328485 dvd_617_base
      ⟨604164242, by norm_num⟩
    have heq : 77 * 1208328485 = 93041293345 := by norm_num
    rwa [heq] at h
  have hd2731 : 2731 ∣ (2 ^ 93041293345 + 1) := by
    have h := dvd_two_pow_add_one_of_dvd_odd_quot 2731 13 7157022565 dvd_2731_base
      ⟨3578511282, by norm_num⟩
    have heq : 13 * 7157022565 = 93041293345 := by norm_num
    rwa [heq] at h
  have hd_3_131 : (3 * 131) ∣ (2 ^ 93041293345 + 1) :=
    (by norm_num : Nat.Coprime 3 131).mul_dvd_of_dvd_of_dvd hd3 hd131
  have hd_3_131_281 : (3 * 131 * 281) ∣ (2 ^ 93041293345 + 1) :=
    (by norm_num : Nat.Coprime (3 * 131) 281).mul_dvd_of_dvd_of_dvd hd_3_131 hd281
  have hd_4 : (3 * 131 * 281 * 617) ∣ (2 ^ 93041293345 + 1) :=
    (by norm_num : Nat.Coprime (3 * 131 * 281) 617).mul_dvd_of_dvd_of_dvd hd_3_131_281 hd617
  have hd_5 : (3 * 131 * 281 * 617 * 2731) ∣ (2 ^ 93041293345 + 1) :=
    (by norm_num : Nat.Coprime (3 * 131 * 281 * 617) 2731).mul_dvd_of_dvd_of_dvd hd_4 hd2731
  have hprod : 3 * 131 * 281 * 617 * 2731 = 186082586691 := by norm_num
  rwa [hprod] at hd_5

/-- Smallest counterexample witness (`k = 93,041,293,345`, `n = 2*k + 1 = 186,082,586,691 =
3 * 131 * 281 * 617 * 2731`, `A244628(1138)` = `A376255(2)`): `n` belongs to `A294912`,
while `(3 * n) ∣ (2 ^ k + 1)` fails. -/
theorem c085_witness :
    inA294912 186082586691 ∧ ¬ ((3 * 186082586691) ∣ (2 ^ 93041293345 + 1)) := by
  have hn : 2 * 93041293345 + 1 = 186082586691 := by norm_num
  have hgt : 1 < 93041293345 := by norm_num
  have hodd : 93041293345 % 2 = 1 := by norm_num
  constructor
  · rw [← hn, inA294912_odd_iff 93041293345 hgt]
    exact ⟨hodd, by rw [hn]; exact witness_dvd⟩
  · rw [← hn]
    exact not_three_mul_dvd_of_three_dvd 93041293345 ⟨62027528897, by norm_num⟩

private lemma witness_not_prime : ¬Nat.Prime (2 * 93041293345 + 1) := by
  have hfac : 2 * 93041293345 + 1 = 3 * 62027528897 := by norm_num
  rw [hfac, Nat.prime_mul_iff]
  rintro (⟨_, h⟩ | ⟨_, h⟩) <;> norm_num at h

/-- Formal refutation of Hilko Koning's Dec 09 2019 `A294912` composite characterization
(`PIN-C085.md` v1): the biconditional fails at `k = 93,041,293,345`. -/
theorem c085_refutation :
    ¬ (∀ k : ℕ, 1 < k → ¬Nat.Prime (2 * k + 1) →
      (inA294912 (2 * k + 1) ↔ (3 * (2 * k + 1)) ∣ (2 ^ k + 1))) := by
  intro hall
  have hgt : 1 < 93041293345 := by norm_num
  have hiff := hall 93041293345 hgt witness_not_prime
  have hn : 2 * 93041293345 + 1 = 186082586691 := by norm_num
  rw [hn] at hiff
  exact c085_witness.2 (hiff.mp c085_witness.1)

private lemma mod_three_mul_eq_two_mul {n x : ℕ} (hn0 : 0 < n) (hn9 : n % 9 = 6)
    (hdvd : n ∣ x) (hx9 : x % 9 = 3) : x % (3 * n) = 2 * n := by
  rcases hdvd with ⟨q, hq⟩
  have hq3 : q % 3 = 2 := by
    have hmul : (n * q) % 9 = 3 := by rwa [← hq]
    have hstep : (6 * (q % 9)) % 9 = 3 := by
      rw [Nat.mul_mod, hn9] at hmul
      exact hmul
    omega
  obtain ⟨t, ht⟩ : ∃ t, q = 3 * t + 2 := ⟨q / 3, by omega⟩
  rw [hq, ht]
  have hrew : n * (3 * t + 2) = 2 * n + (3 * n) * t := by ring
  rw [hrew, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

/-- Exact non-zero remainder of `2 ^ 93041293345 + 1` modulo `3 * 186082586691`:
`(2 ^ k + 1) mod (3 * n) = 2 * n = 372,165,173,382`. -/
theorem c085_witness_mod_3n :
    (2 ^ 93041293345 + 1) % (3 * 186082586691) = 2 * 186082586691 :=
  mod_three_mul_eq_two_mul (by norm_num) (by norm_num) witness_dvd
    (mod_nine_of_mod_six_eq_one 93041293345 (by norm_num))

/-! ### Section 4: Structural extensions (even exclusion, boundary sharpness, `A244628` identity,
`3 * p` / `3 * p ^ 2` impossibility, and positive composite non-vacuity) -/

/-- Even integers `n = 2 * m ≥ 2` never satisfy `inA294912` (rejected by Congruence 1). -/
theorem inA294912_even_false (m : ℕ) (hm : 1 ≤ m) : ¬ inA294912 (2 * m) := by
  rintro ⟨hc1, _, _, _⟩
  have h2pow : 2 ∣ 2 ^ (2 * m - 1) := dvd_pow_self 2 (by omega)
  have h2n : 2 ∣ 2 * m := dvd_mul_right 2 m
  have h2mod : 2 ∣ (2 ^ (2 * m - 1)) % (2 * m) := (Nat.dvd_mod_iff h2n).mpr h2pow
  have h1mod : 1 % (2 * m) = 1 := Nat.mod_eq_of_lt (by omega)
  rw [Nat.ModEq, h1mod] at hc1
  rw [hc1] at h2mod
  omega

/-- Sharpness of `1 < k` at `k = 0` (`n = 1`): under bare `Nat.ModEq`, `inA294912 1` holds
while `¬Nat.Prime 1` and `¬ (3 * 1 ∣ 2 ^ 0 + 1)`. -/
theorem inA294912_one :
    inA294912 1 ∧ ¬Nat.Prime 1 ∧ ¬ ((3 * 1) ∣ (2 ^ 0 + 1)) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, Nat.not_prime_one, by norm_num⟩ <;>
    simp [Nat.ModEq]

/-- Sharpness of `1 < k` at `k = 1` (`n = 3`): prime `n = 3` satisfies `inA294912 3`
while `¬ (3 * 3 ∣ 2 ^ 1 + 1)`. -/
theorem inA294912_three :
    inA294912 3 ∧ Nat.Prime 3 ∧ ¬ ((3 * 3) ∣ (2 ^ 1 + 1)) := by
  refine ⟨⟨by decide, by decide, by decide, by decide⟩, Nat.prime_three, by norm_num⟩

/-- Every odd prime factor of `2 ^ (2 * m + 1) + 1` is congruent to `1` or `3` modulo `8`
(since `(2 ^ (m + 1)) ^ 2 = -2` in `ZMod p`). -/
theorem prime_dvd_two_pow_odd_add_one_mod_eight {p m : ℕ}
    (hp : Nat.Prime p) (hdvd : p ∣ (2 ^ (2 * m + 1) + 1)) :
    p % 8 = 1 ∨ p % 8 = 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro h2
    subst h2
    have heven : 2 ∣ 2 ^ (2 * m + 1) := dvd_pow_self 2 (by omega)
    have h1 : 2 ∣ 1 := (Nat.dvd_add_right heven).mp hdvd
    omega
  rw [← ZMod.exists_sq_eq_neg_two_iff hp2]
  refine ⟨(2 : ZMod p) ^ (m + 1), ?_⟩
  have hz : ((2 ^ (2 * m + 1) + 1 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  have h2pow : (2 : ZMod p) ^ (2 * m + 1) = -1 := by
    push_cast at hz
    exact eq_neg_of_add_eq_zero_left hz
  calc
    (-2 : ZMod p) = 2 * (-1) := by ring
    _ = 2 * (2 : ZMod p) ^ (2 * m + 1) := by rw [h2pow]
    _ = (2 : ZMod p) ^ (m + 1) * (2 : ZMod p) ^ (m + 1) := by
          rw [← pow_add, ← pow_succ']
          congr 1
          omega

/-- Any positive integer whose prime factors all lie in `{1, 3} mod 8` itself lies in
`{1, 3} mod 8` (since `{1, 3}` is a subgroup of `(ℤ/8ℤ)ˣ`). -/
private lemma mod_eight_one_or_three_of_primes :
    ∀ n : ℕ, 0 < n → (∀ p : ℕ, Nat.Prime p → p ∣ n → p % 8 = 1 ∨ p % 8 = 3) →
      n % 8 = 1 ∨ n % 8 = 3 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hpos hfac
    by_cases h1 : n = 1
    · left; omega
    · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
      obtain ⟨q, rfl⟩ := hpn
      have hqpos : 0 < q := by
        rcases eq_or_lt_of_le (Nat.zero_le q) with rfl | h
        · simp at hpos
        · exact h
      have hqlt : q < p * q := lt_mul_of_one_lt_left hqpos hp.one_lt
      have hp8 : p % 8 = 1 ∨ p % 8 = 3 := hfac p hp (dvd_mul_right p q)
      have hq8 : q % 8 = 1 ∨ q % 8 = 3 :=
        ih q hqlt hqpos (fun r hr hrq => hfac r hr (dvd_mul_of_dvd_right hrq p))
      rw [Nat.mul_mod]
      rcases hp8 with h | h <;> rcases hq8 with h' | h' <;> rw [h, h'] <;> norm_num

/-- Step 6 (SCOPING §1.2): Automatic upgrade from `n ≡ 3 [MOD 4]` to `n ≡ 3 [MOD 8]` for every
term `2 * k + 1 ∈ A294912` (`k > 1`). -/
theorem inA294912_mod_eight (k : ℕ) (hk : 1 < k) (h : inA294912 (2 * k + 1)) :
    (2 * k + 1) % 8 = 3 := by
  rcases (inA294912_odd_iff k hk).mp h with ⟨hodd, hdvd⟩
  obtain ⟨m, hm⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
  have h13 : (2 * k + 1) % 8 = 1 ∨ (2 * k + 1) % 8 = 3 := by
    apply mod_eight_one_or_three_of_primes (2 * k + 1) (by omega)
    intro p hp hpn
    exact prime_dvd_two_pow_odd_add_one_mod_eight hp (by rw [← hm]; exact dvd_trans hpn hdvd)
  omega

/-- Exact identity between composite terms of OEIS `A294912` and OEIS `A244628`
(`Composite n such that n ≡ 3 (mod 8) and 2^((n-1)/2) ≡ -1 (mod n)`). -/
theorem c085_a244628_iff (k : ℕ) (hk : 1 < k) (hcomp : ¬Nat.Prime (2 * k + 1)) :
    inA294912 (2 * k + 1) ↔ ((2 * k + 1) % 8 = 3 ∧ (2 * k + 1) ∣ (2 ^ k + 1)) := by
  constructor
  · intro hin
    exact ⟨inA294912_mod_eight k hk hin, ((c085_positive_characterization k hk hcomp).mp hin).2⟩
  · rintro ⟨h8, hdvd⟩
    exact (c085_positive_characterization k hk hcomp).mpr ⟨by omega, hdvd⟩

/-- Structural exclusion (SCOPING §4.2): No semiprime `3 * p` (`p > 3` prime) belongs to `A294912`. -/
theorem c085_no_3p (p : ℕ) (hp : Nat.Prime p) (hp3 : 3 < p) : ¬ inA294912 (3 * p) := by
  intro hin
  have : Fact p.Prime := ⟨hp⟩
  have hp_odd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with rfl | h
    · omega
    · exact h
  obtain ⟨r, hr⟩ : ∃ r, p = 2 * r + 1 := ⟨p / 2, by omega⟩
  have h3p : 3 * p = 2 * (3 * r + 1) + 1 := by omega
  rw [h3p] at hin
  rcases (inA294912_odd_iff (3 * r + 1) (by omega)).mp hin with ⟨hodd, hdvd⟩
  have hpdvd : p ∣ (2 ^ (3 * r + 1) + 1) := dvd_trans ⟨3, by omega⟩ hdvd
  have hz : ((2 ^ (3 * r + 1) + 1 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hpdvd
  push_cast at hz
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
    have := Nat.le_of_dvd (by decide) h2
    omega
  have hflt : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hexp : 3 * r + 1 = (p - 1) + (r + 1) := by omega
  have hsq : ((2 : ZMod p) ^ r) ^ 2 = 1 := by
    rw [← pow_mul]
    have h2r : r * 2 = p - 1 := by omega
    rw [h2r, hflt]
  have hpm : (2 : ZMod p) ^ r = 1 ∨ (2 : ZMod p) ^ r = -1 := sq_eq_one_iff.mp hsq
  have hpow : (2 : ZMod p) ^ (3 * r + 1) = 2 * (2 : ZMod p) ^ r := by
    rw [hexp, pow_add, hflt, one_mul, pow_succ']
  rw [hpow] at hz
  rcases hpm with h1 | hm1
  · rw [h1, mul_one] at hz
    have h3zero : ((3 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination hz
    have hp3dvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h3zero
    have := Nat.le_of_dvd (by decide) hp3dvd
    omega
  · rw [hm1] at hz
    have hneg1 : (-1 : ZMod p) = 0 := by linear_combination hz
    have h10 : (1 : ZMod p) = 0 := by linear_combination -hneg1
    exact one_ne_zero h10

/-- Structural exclusion (SCOPING §4.2): No integer `3 * p ^ 2` (`p > 3` prime) belongs to `A294912`. -/
theorem c085_no_3p_sq (p : ℕ) (hp : Nat.Prime p) (hp3 : 3 < p) : ¬ inA294912 (3 * p ^ 2) := by
  intro hin
  have : Fact p.Prime := ⟨hp⟩
  have hp_odd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with rfl | h
    · omega
    · exact h
  obtain ⟨r, hr⟩ : ∃ r, p = 2 * r + 1 := ⟨p / 2, by omega⟩
  set k := 6 * r ^ 2 + 6 * r + 1
  have h3p2 : 3 * p ^ 2 = 2 * k + 1 := by
    rw [hr]
    ring
  rw [h3p2] at hin
  rcases (inA294912_odd_iff k (by nlinarith)).mp hin with ⟨_, hdvd⟩
  have hpdvd : p ∣ (2 ^ k + 1) := dvd_trans ⟨3 * p, by rw [← h3p2]; ring⟩ hdvd
  have hz : ((2 ^ k + 1 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hpdvd
  push_cast at hz
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
    have := Nat.le_of_dvd (by decide) h2
    omega
  have hflt : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hk_eq : k = (p - 1) * (3 * r + 3) + 1 := by
    have hpm1 : p - 1 = 2 * r := by omega
    rw [hpm1]
    ring
  have hpow : (2 : ZMod p) ^ k = 2 := by
    rw [hk_eq, pow_succ, pow_mul, hflt, one_pow, one_mul]
  rw [hpow] at hz
  have h3zero : ((3 : ℕ) : ZMod p) = 0 := by
    push_cast
    linear_combination hz
  have hp3dvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h3zero
  have := Nat.le_of_dvd (by decide) hp3dvd
  omega

/-- Non-vacuity witness for the positive regime (`a(1)` of `A244628`, `A294912(9969)`):
`k = 238,485`, `n = 476,971 = 11 * 131 * 331` is an odd composite satisfying both
`inA294912 n` and `(3 * n) ∣ (2 ^ k + 1)`. -/
theorem c085_first_positive_composite :
    1 < 238485 ∧ ¬Nat.Prime (2 * 238485 + 1) ∧
      inA294912 (2 * 238485 + 1) ∧ (3 * (2 * 238485 + 1)) ∣ (2 ^ 238485 + 1) := by
  have hgt : 1 < 238485 := by norm_num
  have hodd : 238485 % 2 = 1 := by norm_num
  have hnot3 : ¬ 3 ∣ (2 * 238485 + 1) := by norm_num
  have hnotprime : ¬Nat.Prime (2 * 238485 + 1) := by
    have hfac : 2 * 238485 + 1 = 11 * 43361 := by norm_num
    rw [hfac, Nat.prime_mul_iff]
    rintro (⟨_, h⟩ | ⟨_, h⟩) <;> norm_num at h
  have hd11 : 11 ∣ (2 ^ 238485 + 1) := by
    have h := dvd_two_pow_add_one_of_dvd_odd_quot 11 5 47697 ⟨3, by norm_num⟩
      ⟨23848, by norm_num⟩
    have heq : 5 * 47697 = 238485 := by norm_num
    rwa [heq] at h
  have hd131 : 131 ∣ (2 ^ 238485 + 1) := by
    have h := dvd_two_pow_add_one_of_dvd_odd_quot 131 65 3669 dvd_131_base
      ⟨1834, by norm_num⟩
    have heq : 65 * 3669 = 238485 := by norm_num
    rwa [heq] at h
  have hd331 : 331 ∣ (2 ^ 238485 + 1) := by
    have h := dvd_two_pow_add_one_of_dvd_odd_quot 331 15 15899 ⟨99, by norm_num⟩
      ⟨7949, by norm_num⟩
    have heq : 15 * 15899 = 238485 := by norm_num
    rwa [heq] at h
  have hd_11_131 : (11 * 131) ∣ (2 ^ 238485 + 1) :=
    (by norm_num : Nat.Coprime 11 131).mul_dvd_of_dvd_of_dvd hd11 hd131
  have hd_all : (11 * 131 * 331) ∣ (2 ^ 238485 + 1) :=
    (by norm_num : Nat.Coprime (11 * 131) 331).mul_dvd_of_dvd_of_dvd hd_11_131 hd331
  have hprod : 11 * 131 * 331 = 2 * 238485 + 1 := by norm_num
  rw [hprod] at hd_all
  have hin : inA294912 (2 * 238485 + 1) :=
    (inA294912_odd_iff 238485 hgt).mpr ⟨hodd, hd_all⟩
  have hkoning : (3 * (2 * 238485 + 1)) ∣ (2 ^ 238485 + 1) :=
    (koning_iff_of_not_three_dvd 238485 hgt hnot3).mp hin
  exact ⟨hgt, hnotprime, hin, hkoning⟩

end C085
