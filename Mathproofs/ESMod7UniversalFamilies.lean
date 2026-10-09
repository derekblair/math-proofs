/-
  ESMod7UniversalFamilies.lean — Lean kernel for R176's ES-sieve structural results
  (Round 176 dossier, 2026-10-08).

  Machine-checked statements (Lean 4.34.1 + Mathlib v4.34.1):

  (a) R176 §1b — the three mod-7 universal families
      (c,h,a,b) = (3,2,1,21) on s≡3, (6,1,2,21) on s≡5, (4,1,1,14) on s≡6 (mod 7),
      where s = 24k₀+1 and x₀ = 6k₀+c. For each family: the fiber direction
      (s≡3/5/6 ⟹ k₀≡3/6/4), the framework premise ab ∣ h·gcd(2310,x₀), and
      a+b = m·h exact.
  (b) R176 §2a — the mod-13 fiber-pinning lemma: for a b=13 family,
      13 ∣ x₀ = 6k₀+c forces k₀ ≡ 2c and s = 24k₀+1 ≡ 9c+1 (mod 13),
      with R55's two instances (2,2,1,13) → k₀≡4 → s≡6 and
      (4,1,2,13) → k₀≡8 → s≡11.

  Honest scope: R38's framework theorem (these premises ⟹ a valid Erdős–Straus
  identity 4/(9240t+s) = Σ1/(·) for all t≥0 on the fiber) is CITED, not
  re-formalized here. The 165-class coverage sweep and the 11/11 fiber tables
  stay [COMPUTED] (r176_qr7c.py / r176_mod13.py). The one-j-per-r-class count
  stays [PROVED*] (algebraic + JSON cross-check in the dossier).
-/

import Mathlib

namespace ESMod7UniversalFamilies

/-! ## Fiber directions: s = 24k₀+1 ≡ 3k₀+1 (mod 7) -/

/-- s ≡ 3 (mod 7) ⟹ k₀ ≡ 3: 3k₀+1 ≡ 3 ⟺ 3k₀ ≡ 2 ⟺ k₀ ≡ 3. -/
theorem fiber_dir_3 (k₀ : ℕ) (h : (24*k₀+1) % 7 = 3) : k₀ % 7 = 3 := by
  omega

/-- s ≡ 5 (mod 7) ⟹ k₀ ≡ 6: 3k₀+1 ≡ 5 ⟺ 3k₀ ≡ 4 ⟺ k₀ ≡ 6. -/
theorem fiber_dir_5 (k₀ : ℕ) (h : (24*k₀+1) % 7 = 5) : k₀ % 7 = 6 := by
  omega

/-- s ≡ 6 (mod 7) ⟹ k₀ ≡ 4: 3k₀+1 ≡ 6 ⟺ 3k₀ ≡ 5 ⟺ k₀ ≡ 4. -/
theorem fiber_dir_6 (k₀ : ℕ) (h : (24*k₀+1) % 7 = 6) : k₀ % 7 = 4 := by
  omega

/-! ## Family 1: (c,h,a,b) = (3,2,1,21), x₀ = 6k₀+3, on s ≡ 3 -/

/-- 7 ∣ x₀ on the pinned fiber: k₀ ≡ 3 (mod 7) ⟹ 7 ∣ 6k₀+3. -/
theorem fam1_seven_dvd (k₀ : ℕ) (h : k₀ % 7 = 3) : 7 ∣ 6*k₀+3 := by
  omega

/-- Framework premise: ab ∣ h·gcd(2310,x₀), i.e. 1·21 ∣ 2·gcd(2310, 6k₀+3).
    Needs 21 ∣ x₀ (3 ∣ x₀ always; 7 ∣ x₀ on the fiber) and 21 ∣ 2310. -/
theorem fam1_premise (k₀ : ℕ) (h : k₀ % 7 = 3) :
    1*21 ∣ 2 * Nat.gcd 2310 (6*k₀+3) := by
  have h3 : 3 ∣ 6*k₀+3 := ⟨2*k₀+1, by ring⟩
  have h7 : 7 ∣ 6*k₀+3 := by omega
  have h21x : 21 ∣ 6*k₀+3 := by
    have h37 := (by decide : Nat.Coprime 3 7).mul_dvd_of_dvd_of_dvd h3 h7
    simpa using h37
  have h21w : 21 ∣ 2310 := by decide
  have h := (Nat.dvd_gcd h21w h21x).mul_left 2
  simpa using h

/-- a+b = m·h exact: 1+21 = 11·2. -/
theorem fam1_ab_mh : 1+21 = 11*2 := by decide

/-- Family 1 packaged: on s ≡ 3 (mod 7), (3,2,1,21) meets the framework premises. -/
theorem fam1_universal (k₀ : ℕ) (hs : (24*k₀+1) % 7 = 3) :
    k₀ % 7 = 3 ∧ 1*21 ∣ 2 * Nat.gcd 2310 (6*k₀+3) ∧ 1+21 = 11*2 :=
  ⟨fiber_dir_3 k₀ hs, fam1_premise k₀ (fiber_dir_3 k₀ hs), fam1_ab_mh⟩

/-! ## Family 2: (c,h,a,b) = (6,1,2,21), x₀ = 6k₀+6, on s ≡ 5 -/

/-- 7 ∣ x₀ on the pinned fiber: k₀ ≡ 6 (mod 7) ⟹ 7 ∣ 6k₀+6. -/
theorem fam2_seven_dvd (k₀ : ℕ) (h : k₀ % 7 = 6) : 7 ∣ 6*k₀+6 := by
  omega

/-- Framework premise: ab ∣ h·gcd(2310,x₀), i.e. 2·21 ∣ 1·gcd(2310, 6k₀+6).
    Needs 42 ∣ x₀ (7 ∣ x₀ on the fiber; 6 ∣ x₀ always) and 42 ∣ 2310. -/
theorem fam2_premise (k₀ : ℕ) (h : k₀ % 7 = 6) :
    2*21 ∣ 1 * Nat.gcd 2310 (6*k₀+6) := by
  have h7 : 7 ∣ 6*k₀+6 := by omega
  have h6 : 6 ∣ 6*k₀+6 := ⟨k₀+1, by ring⟩
  have h42x : 42 ∣ 6*k₀+6 := by
    have h76 := (by decide : Nat.Coprime 7 6).mul_dvd_of_dvd_of_dvd h7 h6
    simpa using h76
  have h42w : 42 ∣ 2310 := by decide
  have h := (Nat.dvd_gcd h42w h42x).mul_left 1
  simpa using h

/-- a+b = m·h exact: 2+21 = 23·1. -/
theorem fam2_ab_mh : 2+21 = 23*1 := by decide

/-- Family 2 packaged: on s ≡ 5 (mod 7), (6,1,2,21) meets the framework premises. -/
theorem fam2_universal (k₀ : ℕ) (hs : (24*k₀+1) % 7 = 5) :
    k₀ % 7 = 6 ∧ 2*21 ∣ 1 * Nat.gcd 2310 (6*k₀+6) ∧ 2+21 = 23*1 :=
  ⟨fiber_dir_5 k₀ hs, fam2_premise k₀ (fiber_dir_5 k₀ hs), fam2_ab_mh⟩

/-! ## Family 3: (c,h,a,b) = (4,1,1,14), x₀ = 6k₀+4, on s ≡ 6 -/

/-- 7 ∣ x₀ on the pinned fiber: k₀ ≡ 4 (mod 7) ⟹ 7 ∣ 6k₀+4. -/
theorem fam3_seven_dvd (k₀ : ℕ) (h : k₀ % 7 = 4) : 7 ∣ 6*k₀+4 := by
  omega

/-- Framework premise: ab ∣ h·gcd(2310,x₀), i.e. 1·14 ∣ 1·gcd(2310, 6k₀+4).
    Needs 14 ∣ x₀ (7 ∣ x₀ on the fiber; 2 ∣ x₀ always) and 14 ∣ 2310. -/
theorem fam3_premise (k₀ : ℕ) (h : k₀ % 7 = 4) :
    1*14 ∣ 1 * Nat.gcd 2310 (6*k₀+4) := by
  have h7 : 7 ∣ 6*k₀+4 := by omega
  have h2 : 2 ∣ 6*k₀+4 := ⟨3*k₀+2, by ring⟩
  have h14x : 14 ∣ 6*k₀+4 := by
    have h72 := (by decide : Nat.Coprime 7 2).mul_dvd_of_dvd_of_dvd h7 h2
    simpa using h72
  have h14w : 14 ∣ 2310 := by decide
  have h := (Nat.dvd_gcd h14w h14x).mul_left 1
  simpa using h

/-- a+b = m·h exact: 1+14 = 15·1. -/
theorem fam3_ab_mh : 1+14 = 15*1 := by decide

/-- Family 3 packaged: on s ≡ 6 (mod 7), (4,1,1,14) meets the framework premises. -/
theorem fam3_universal (k₀ : ℕ) (hs : (24*k₀+1) % 7 = 6) :
    k₀ % 7 = 4 ∧ 1*14 ∣ 1 * Nat.gcd 2310 (6*k₀+4) ∧ 1+14 = 15*1 :=
  ⟨fiber_dir_6 k₀ hs, fam3_premise k₀ (fiber_dir_6 k₀ hs), fam3_ab_mh⟩

/-! ## Mod-13 fiber-pinning lemma (R176 §2a)

For a b=13 family with 13 ∤ h, the framework condition ab ∣ h·g₀ forces
13 ∣ x₀ = 6k₀+c (13 ∣ ab, 13 ∤ h). The pinning below takes that forced
divisibility as its hypothesis — the elementary arithmetic core. -/

/-- Fiber-pinning: 13 ∣ 6k₀+c ⟹ k₀ ≡ 2c (mod 13), since 6⁻¹ ≡ 11 gives
    k₀ ≡ -11c ≡ 2c; hence s = 24k₀+1 ≡ 11·2c+1 ≡ 9c+1 (mod 13). -/
theorem fiber_pin (k₀ c : ℕ) (h : 13 ∣ 6*k₀+c) :
    k₀ % 13 = (2*c) % 13 ∧ (24*k₀+1) % 13 = (9*c+1) % 13 := by
  constructor <;> omega

/-- R55 instance (2,2,1,13): c=2 pins k₀ ≡ 4, hence s ≡ 6 (mod 13). -/
theorem fiber_pin_c2 (k₀ : ℕ) (h : 13 ∣ 6*k₀+2) :
    k₀ % 13 = 4 ∧ (24*k₀+1) % 13 = 6 := by
  obtain ⟨h1, h2⟩ := fiber_pin k₀ 2 h
  constructor <;> omega

/-- R55 instance (4,1,2,13): c=4 pins k₀ ≡ 8, hence s ≡ 11 (mod 13). -/
theorem fiber_pin_c4 (k₀ : ℕ) (h : 13 ∣ 6*k₀+4) :
    k₀ % 13 = 8 ∧ (24*k₀+1) % 13 = 11 := by
  obtain ⟨h1, h2⟩ := fiber_pin k₀ 4 h
  constructor <;> omega

end ESMod7UniversalFamilies
