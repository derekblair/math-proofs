import Mathlib

/-!
# T1 two-case obstruction (Rounds 134, 150)

Formalizes R134's Theorem 2: for a ≥ 1, d ≥ 1 and f ∣ 4a²d+1, the congruence
x² ≡ −f (mod 4ad) has NO integer solution.

Two-case reciprocity argument (R134 §3):

- **Step 1 (2-adic).** Any solution has x odd and f ≡ 3 (mod 4); if 8 ∣ 4ad
  then f ≡ 7 (mod 8) (`f_mod4`, `f_mod8`).
- Write d = 2^t·d₁ with d₁ odd.
- **Case A (d₁ > 1).** x² ≡ −f (mod d₁) forces `jacobiSym (−f) d₁ = 1`
  (via `coprime_x_d1` + `jacobiSym.sq_one'`), but the reciprocity computation
  (`jacobi_neg_f`) gives `(-1)^E` with
  E = d₁/2 + (f/2)(d₁/2) + t((f²−1)/8) + f/2. E even forces
  `t·((f²−1)/8)` odd, i.e. t ≥ 1 and f ≡ 3,5 (mod 8) (`parity_core`) —
  contradicting f ≡ 7 (mod 8), since t ≥ 1 gives 8 ∣ 4ad.
- **Case B (d₁ = 1).** (2a)²·(−d) ≡ 1 (mod f) gives `jacobiSym (−d) f = 1`
  (`jacobi_neg_d`), but −d = −2^t gives `(-1)^(f/2 + t((f²−1)/8))`
  (`jacobi_two`); the same parity finish applies.

Corollary: no T1 class contains a square — R130's prime-square obstruction for
T1, strengthened to all squares, as the Lean-checked kernel.
-/

namespace EST1TwoCase

/-- Odd squares are 1 mod 8. -/
lemma sq_one_mod8 {n : ℕ} (h : Odd n) : ((n : ℤ) ^ 2) % (8 : ℤ) = 1 := by
  obtain ⟨k, hk⟩ := h
  have hcast : (n : ℤ) = 2 * (k : ℤ) + 1 := by exact_mod_cast hk
  obtain ⟨j, hj⟩ := Int.even_mul_succ_self (k : ℤ)
  have e2 : (k : ℤ) ^ 2 + (k : ℤ) = 2 * j := by linear_combination hj
  have hsq : (n : ℤ) ^ 2 = 8 * j + 1 := by
    have e1 : (n : ℤ) ^ 2 = 4 * ((k : ℤ) ^ 2 + (k : ℤ)) + 1 := by rw [hcast]; ring
    rw [e1, e2]; ring
  rw [hsq]; omega

/-- Odd squares are 1 mod 4. -/
lemma sq_one_mod4 {n : ℕ} (h : Odd n) : ((n : ℤ) ^ 2) % (4 : ℤ) = 1 := by
  obtain ⟨k, hk⟩ := h
  have hcast : (n : ℤ) = 2 * (k : ℤ) + 1 := by exact_mod_cast hk
  have hsq : (n : ℤ) ^ 2 = 4 * ((k : ℤ) ^ 2 + (k : ℤ)) + 1 := by rw [hcast]; ring
  rw [hsq]; omega

/-- Parity of (f²−1)/8 for odd f: odd iff f ≡ 3 or 5 (mod 8). -/
lemma odd_half_sq {f : ℕ} (h : Odd f) :
    Odd ((f ^ 2 - 1) / 8) ↔ (f % 8 = 3 ∨ f % 8 = 5) := by
  have h178 : f % 8 = 1 ∨ f % 8 = 3 ∨ f % 8 = 5 ∨ f % 8 = 7 := by
    have h2 := Nat.odd_iff.mp h; omega
  rcases h178 with hr | hr | hr | hr
  · have hfm : f = 8 * (f / 8) + 1 := by omega
    have hdiv : (f ^ 2 - 1) / 8 = 8 * ((f / 8) ^ 2) + 2 * (f / 8) := by
      have h1 : f ^ 2 = 8 * (8 * ((f / 8) ^ 2) + 2 * (f / 8)) + 1 := by
        have hsq : f ^ 2 = (8 * (f / 8) + 1) ^ 2 := congrArg (· ^ 2) hfm
        have hexpand : (8 * (f / 8) + 1) ^ 2 = 8 * (8 * ((f / 8) ^ 2) + 2 * (f / 8)) + 1 := by ring
        rw [hsq]; exact hexpand
      have h2 : f ^ 2 - 1 = 8 * (8 * ((f / 8) ^ 2) + 2 * (f / 8)) := by
        rw [h1]
        exact Nat.add_sub_cancel _ _
      rw [h2]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    rw [hdiv, Nat.odd_iff]
    clear hdiv hfm h
    constructor <;> intro h <;> omega
  · have hfm : f = 8 * (f / 8) + 3 := by omega
    have hdiv : (f ^ 2 - 1) / 8 = 8 * ((f / 8) ^ 2) + 6 * (f / 8) + 1 := by
      have h1 : f ^ 2 = 8 * (8 * ((f / 8) ^ 2) + 6 * (f / 8) + 1) + 1 := by
        have hsq : f ^ 2 = (8 * (f / 8) + 3) ^ 2 := congrArg (· ^ 2) hfm
        have hexpand : (8 * (f / 8) + 3) ^ 2 = 8 * (8 * ((f / 8) ^ 2) + 6 * (f / 8) + 1) + 1 := by ring
        rw [hsq]; exact hexpand
      have h2 : f ^ 2 - 1 = 8 * (8 * ((f / 8) ^ 2) + 6 * (f / 8) + 1) := by
        rw [h1]
        exact Nat.add_sub_cancel _ _
      rw [h2]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    rw [hdiv, Nat.odd_iff]
    clear hdiv hfm h
    constructor <;> intro h <;> omega
  · have hfm : f = 8 * (f / 8) + 5 := by omega
    have hdiv : (f ^ 2 - 1) / 8 = 8 * ((f / 8) ^ 2) + 10 * (f / 8) + 3 := by
      have h1 : f ^ 2 = 8 * (8 * ((f / 8) ^ 2) + 10 * (f / 8) + 3) + 1 := by
        have hsq : f ^ 2 = (8 * (f / 8) + 5) ^ 2 := congrArg (· ^ 2) hfm
        have hexpand : (8 * (f / 8) + 5) ^ 2 = 8 * (8 * ((f / 8) ^ 2) + 10 * (f / 8) + 3) + 1 := by ring
        rw [hsq]; exact hexpand
      have h2 : f ^ 2 - 1 = 8 * (8 * ((f / 8) ^ 2) + 10 * (f / 8) + 3) := by
        rw [h1]
        exact Nat.add_sub_cancel _ _
      rw [h2]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    rw [hdiv, Nat.odd_iff]
    clear hdiv hfm h
    constructor <;> intro h <;> omega
  · have hfm : f = 8 * (f / 8) + 7 := by omega
    have hdiv : (f ^ 2 - 1) / 8 = 8 * ((f / 8) ^ 2) + 14 * (f / 8) + 6 := by
      have h1 : f ^ 2 = 8 * (8 * ((f / 8) ^ 2) + 14 * (f / 8) + 6) + 1 := by
        have hsq : f ^ 2 = (8 * (f / 8) + 7) ^ 2 := congrArg (· ^ 2) hfm
        have hexpand : (8 * (f / 8) + 7) ^ 2 = 8 * (8 * ((f / 8) ^ 2) + 14 * (f / 8) + 6) + 1 := by ring
        rw [hsq]; exact hexpand
      have h2 : f ^ 2 - 1 = 8 * (8 * ((f / 8) ^ 2) + 14 * (f / 8) + 6) := by
        rw [h1]
        exact Nat.add_sub_cancel _ _
      rw [h2]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    rw [hdiv, Nat.odd_iff]
    clear hdiv hfm h
    constructor <;> intro h <;> omega

/-- (2/f) as a power of −1, via the χ₈ supplementary law. -/
lemma jacobi_two {f : ℕ} (h : Odd f) :
    jacobiSym (2 : ℤ) f = (-1 : ℤ) ^ ((f ^ 2 - 1) / 8) := by
  rw [jacobiSym.at_two h, ZMod.χ₈_nat_eq_if_mod_eight]
  have h2 : f % 2 = 1 := Nat.odd_iff.mp h
  split_ifs
  · omega
  · have hev : Even ((f ^ 2 - 1) / 8) := by
      rw [← Nat.not_odd_iff_even]
      intro hc
      rcases (odd_half_sq h).mp hc with h8 | h8 <;> omega
    exact (Even.neg_one_pow hev).symm
  · have hodd8 : Odd ((f ^ 2 - 1) / 8) := by
      rw [odd_half_sq h]
      have h178 : f % 8 = 1 ∨ f % 8 = 3 ∨ f % 8 = 5 ∨ f % 8 = 7 := by omega
      rcases h178 with h' | h' | h' | h' <;> omega
    exact (Odd.neg_one_pow hodd8).symm

/-- (−1/n) = (−1)^(n/2) for odd n. -/
lemma neg_one_jacobi {n : ℕ} (h : Odd n) :
    jacobiSym (-1 : ℤ) n = (-1 : ℤ) ^ (n / 2) := by
  rw [jacobiSym.at_neg_one h, ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp h)]

/-- f is coprime to 4a²d: any common divisor divides
(4a²d+1) − 4a²d = 1. -/
lemma coprime_f_4a2d {a d f : ℕ} (hdvd : f ∣ 4 * a ^ 2 * d + 1) :
    Nat.Coprime f (4 * a ^ 2 * d) := by
  have key : ∀ g : ℕ, g ∣ f → g ∣ 4 * a ^ 2 * d → g = 1 := by
    intro g hgf hg4
    obtain ⟨e, he⟩ := hdvd
    have hge : g ∣ f * e := dvd_mul_of_dvd_left hgf e
    rw [← he] at hge
    have hsub : g ∣ (4 * a ^ 2 * d + 1 - 4 * a ^ 2 * d) := Nat.dvd_sub hge hg4
    have h1 : 4 * a ^ 2 * d + 1 - 4 * a ^ 2 * d = 1 := by omega
    rw [h1] at hsub
    exact Nat.dvd_one.mp hsub
  show Nat.gcd f (4 * a ^ 2 * d) = 1
  exact key _ (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)

/-- Hence f is coprime to 4ad. -/
lemma coprime_f_4ad {a d f : ℕ} (hdvd : f ∣ 4 * a ^ 2 * d + 1) :
    Nat.Coprime f (4 * a * d) :=
  Nat.Coprime.coprime_dvd_right (show (4 * a * d) ∣ (4 * a ^ 2 * d) from ⟨a, by ring⟩)
    (coprime_f_4a2d hdvd)

/-- And a is coprime to f. -/
lemma coprime_a_f {a d f : ℕ} (hdvd : f ∣ 4 * a ^ 2 * d + 1) :
    Nat.Coprime a f :=
  (Nat.Coprime.coprime_dvd_right (show a ∣ (4 * a ^ 2 * d) from ⟨4 * a * d, by ring⟩)
    (coprime_f_4a2d hdvd)).symm

/-- 2 is coprime to the odd f. -/
lemma coprime_2_f {f : ℕ} (h : Odd f) : Nat.Coprime 2 f := by
  have key : ∀ g : ℕ, g ∣ 2 → g ∣ f → g = 1 := by
    intro g h2 hf2
    have hg_pos : 0 < g := Nat.pos_of_dvd_of_pos h2 (by norm_num)
    have hg_le : g ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    interval_cases g
    · rfl
    · exfalso
      have h2 : f % 2 = 1 := Nat.odd_iff.mp h
      obtain ⟨r, hr⟩ := hf2
      omega
  show Nat.gcd 2 f = 1
  exact key _ (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)

/-- Hence 2a is coprime to f. -/
lemma coprime_2a_f {a d f : ℕ} (hdvd : f ∣ 4 * a ^ 2 * d + 1) (hodd : Odd f) :
    Nat.Coprime (2 * a) f :=
  Nat.Coprime.mul_left (coprime_2_f hodd) (coprime_a_f hdvd)

/-- f ∣ 4a²d+1 forces f odd. -/
lemma odd_f_of_dvd {a d f : ℕ} (hdvd : f ∣ 4 * a ^ 2 * d + 1) : Odd f := by
  obtain ⟨e, he⟩ := hdvd
  have hodd : Odd (f * e) :=
    he ▸ (Even.add_odd ⟨2 * a ^ 2 * d, by ring⟩ odd_one)
  exact (Nat.odd_mul.mp hodd).1

/-- A solution x must be odd (else x² ≡ −f (mod 2) contradicts f odd). -/
lemma odd_x_of {a d f x : ℕ} (hodd_f : Odd f)
    (h_int : (x : ℤ) ^ 2 ≡ (-(f : ℤ)) [ZMOD (((4 * a * d : ℕ)) : ℤ)]) :
    Odd x := by
  by_contra hnx
  rw [Nat.not_odd_iff_even] at hnx
  obtain ⟨k, hk⟩ := hnx
  have hk2 : x = 2 * k := by omega
  have h2dvd : ((2 : ℕ) : ℤ) ∣ ((4 * a * d : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr ⟨2 * a * d, by ring⟩
  have hm2 := Int.ModEq.of_dvd h2dvd h_int
  have hm2' : ((x : ℤ) ^ 2) % (2 : ℤ) = ((-(f : ℤ))) % (2 : ℤ) := hm2
  have hcast : (x : ℤ) = 2 * (k : ℤ) := by exact_mod_cast hk2
  have hsq0 : ((x : ℤ) ^ 2) % (2 : ℤ) = 0 := by
    rw [hcast]
    exact Int.emod_eq_zero_of_dvd ⟨2 * (k : ℤ) ^ 2, by ring⟩
  have hsf1 : ((-(f : ℤ))) % (2 : ℤ) = 1 := by
    obtain ⟨m, hm⟩ := hodd_f
    have hfm : (f : ℤ) = 2 * (m : ℤ) + 1 := by exact_mod_cast hm
    omega
  rw [hsq0, hsf1] at hm2'
  omega

/-- Step 1 (2-adic, mod 4): f ≡ 3 (mod 4). -/
lemma f_mod4 {a d f x : ℕ} (hx : Odd x)
    (h_int : (x : ℤ) ^ 2 ≡ (-(f : ℤ)) [ZMOD (((4 * a * d : ℕ)) : ℤ)]) :
    f % 4 = 3 := by
  have h4dvd : ((4 : ℕ) : ℤ) ∣ ((4 * a * d : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr ⟨a * d, by ring⟩
  have hm4 := Int.ModEq.of_dvd h4dvd h_int
  have hm4' : ((x : ℤ) ^ 2) % (4 : ℤ) = ((-(f : ℤ))) % (4 : ℤ) := hm4
  rw [sq_one_mod4 hx] at hm4'
  omega

/-- Step 1 (2-adic, mod 8): if 8 ∣ 4ad then f ≡ 7 (mod 8). -/
lemma f_mod8 {a d f x : ℕ} (hx : Odd x) (h8 : (8 : ℕ) ∣ 4 * a * d)
    (h_int : (x : ℤ) ^ 2 ≡ (-(f : ℤ)) [ZMOD (((4 * a * d : ℕ)) : ℤ)]) :
    f % 8 = 7 := by
  have h8dvd : ((8 : ℕ) : ℤ) ∣ ((4 * a * d : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr h8
  have hm8 := Int.ModEq.of_dvd h8dvd h_int
  have hm8' : ((x : ℤ) ^ 2) % (8 : ℤ) = ((-(f : ℤ))) % (8 : ℤ) := hm8
  rw [sq_one_mod8 hx] at hm8'
  omega

/-- t ≥ 1 gives 8 ∣ 4ad (via d = 2^t·d₁). -/
lemma eight_dvd_4ad {a d d₁ t : ℕ} (_ha : 1 ≤ a) (ht : 1 ≤ t)
    (hd : d = 2 ^ t * d₁) : (8 : ℕ) ∣ 4 * a * d := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [hd]
  exact ⟨a * (2 ^ s * d₁), by rw [pow_add]; ring⟩

/-- Shared parity finish: t·((f²−1)/8) odd ⟹ t ≥ 1 and f ≡ 3,5 (mod 8). -/
lemma parity_core {f t : ℕ} (h : Odd (t * ((f ^ 2 - 1) / 8))) (hodd_f : Odd f) :
    1 ≤ t ∧ (f % 8 = 3 ∨ f % 8 = 5) := by
  obtain ⟨ht_odd, hq_odd⟩ := Nat.odd_mul.mp h
  have ht1 : t % 2 = 1 := Nat.odd_iff.mp ht_odd
  exact ⟨by omega, (odd_half_sq hodd_f).mp hq_odd⟩

/-- Case A coprimality: gcd(x, d₁) = 1, since a common divisor divides f
(using x² ≡ −f mod d₁) and 4ad, hence divides 1. -/
lemma coprime_x_d1 {x d₁ f a d : ℕ} (hcop : Nat.Coprime f (4 * a * d))
    (hd1_dvd : d₁ ∣ 4 * a * d)
    (h_int : (x : ℤ) ^ 2 ≡ (-(f : ℤ)) [ZMOD (((4 * a * d : ℕ)) : ℤ)]) :
    Nat.Coprime x d₁ := by
  have key : ∀ g : ℕ, g ∣ x → g ∣ d₁ → g = 1 := by
    intro g hgx hgd
    have h3 : g ∣ 4 * a * d := dvd_trans hgd hd1_dvd
    have h3z : ((g : ℕ) : ℤ) ∣ ((4 * a * d : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr h3
    have hmod := Int.ModEq.of_dvd h3z h_int
    have hx0 : (x : ℤ) ≡ 0 [ZMOD ((g : ℕ) : ℤ)] :=
      Int.modEq_zero_iff_dvd.mpr (Int.natCast_dvd_natCast.mpr hgx)
    have hsq : (x : ℤ) ^ 2 ≡ 0 [ZMOD ((g : ℕ) : ℤ)] := by
      have h2 := hx0.mul hx0
      rwa [← pow_two, mul_zero] at h2
    have h0 : (0 : ℤ) ≡ (-(f : ℤ)) [ZMOD ((g : ℕ) : ℤ)] := hsq.symm.trans hmod
    have hgf : g ∣ f := by
      have h1 : ((g : ℕ) : ℤ) ∣ (-(f : ℤ)) - 0 := Int.modEq_iff_dvd.mp h0
      rw [sub_zero] at h1
      have h2 : ((g : ℕ) : ℤ) ∣ (f : ℤ) := dvd_neg.mp h1
      exact Int.natCast_dvd_natCast.mp h2
    have hgdvd : g ∣ Nat.gcd f (4 * a * d) := Nat.dvd_gcd hgf h3
    have hge : Nat.gcd f (4 * a * d) = 1 := hcop
    rw [hge] at hgdvd
    exact Nat.dvd_one.mp hgdvd
  show Nat.gcd x d₁ = 1
  exact key _ (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)

/-- Case A Jacobi computation: (−f/d₁) = (−1)^E with
E = d₁/2 + (f/2)(d₁/2) + t((f²−1)/8) + f/2.
Uses: (−f/d₁) = (−1/d₁)(f/d₁); (f/d₁) by reciprocity; (d₁/f) from
(d/f) = (2/f)^t·(d₁/f) with (d/f) = (−1/f) via 4a²d ≡ −1 (mod f). -/
lemma jacobi_neg_f {f d d₁ t a : ℕ} (hodd_f : Odd f) (hodd_d1 : Odd d₁)
    (hd : d = 2 ^ t * d₁) (hdvd : f ∣ 4 * a ^ 2 * d + 1)
    (hcop_af : Nat.Coprime a f) :
    jacobiSym (-(f : ℤ)) d₁
      = (-1 : ℤ) ^ (d₁ / 2 + (f / 2) * (d₁ / 2) + t * ((f ^ 2 - 1) / 8)
        + f / 2) := by
  have sq_one_a : jacobiSym ((a : ℤ) ^ 2) f = 1 := by
    apply jacobiSym.sq_one'
    rw [Int.gcd_natCast_natCast]
    exact hcop_af
  have e4 : jacobiSym ((d : ℕ) : ℤ) f = (-1 : ℤ) ^ (f / 2) := by
    obtain ⟨e, he⟩ := hdvd
    have hcong : ((4 * a ^ 2 * d : ℕ) : ℤ) % ((f : ℕ) : ℤ)
        = (-1 : ℤ) % ((f : ℕ) : ℤ) := by
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
      have hde : ((4 * a ^ 2 * d : ℕ) : ℤ) - (-1 : ℤ)
          = ((f : ℕ) : ℤ) * ((e : ℕ) : ℤ) := by
        have he' : ((4 * a ^ 2 * d : ℕ) : ℤ) + 1
            = ((f : ℕ) : ℤ) * ((e : ℕ) : ℤ) := by exact_mod_cast he
        linarith
      rw [hde]
      exact Int.emod_eq_zero_of_dvd (dvd_mul_right _ _)
    have hJ := jacobiSym.mod_left' hcong
    have hcast : ((4 * a ^ 2 * d : ℕ) : ℤ)
        = (4 : ℤ) * (a : ℤ) ^ 2 * ((d : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.at_four hodd_f,
      sq_one_a, neg_one_jacobi hodd_f, one_mul, one_mul] at hJ
    exact hJ
  have hd_cast : ((d : ℕ) : ℤ) = (2 : ℤ) ^ t * ((d₁ : ℕ) : ℤ) := by
    rw [hd]; push_cast; ring
  have e3 : jacobiSym ((d : ℕ) : ℤ) f
      = (jacobiSym (2 : ℤ) f) ^ t * jacobiSym ((d₁ : ℕ) : ℤ) f := by
    rw [hd_cast, jacobiSym.mul_left, jacobiSym.pow_left]
  have hJ2 := jacobi_two hodd_f
  have hJ2t2 : (jacobiSym (2 : ℤ) f) ^ t * (jacobiSym (2 : ℤ) f) ^ t = 1 := by
    have hsq : (jacobiSym (2 : ℤ) f) ^ 2 = 1 := by
      rw [hJ2, ← pow_mul]
      exact Even.neg_one_pow ⟨_, by ring⟩
    rw [← pow_add, show t + t = 2 * t from by ring, pow_mul, hsq, one_pow]
  have e5 : jacobiSym ((d₁ : ℕ) : ℤ) f
      = (jacobiSym (2 : ℤ) f) ^ t * jacobiSym ((d : ℕ) : ℤ) f := by
    have hmul := congrArg ((jacobiSym (2 : ℤ) f) ^ t * ·) e3
    rw [← mul_assoc, hJ2t2, one_mul] at hmul
    exact hmul.symm
  have e1 : (-(f : ℤ)) = (-1) * (f : ℤ) := by ring
  have e2 : jacobiSym ((f : ℤ)) d₁
      = (-1 : ℤ) ^ ((f / 2) * (d₁ / 2)) * jacobiSym ((d₁ : ℤ)) f :=
    jacobiSym.quadratic_reciprocity hodd_f hodd_d1
  rw [e1, jacobiSym.mul_left, neg_one_jacobi hodd_d1, e2, e5, e4, hJ2,
    ← pow_mul, mul_comm ((f ^ 2 - 1) / 8) t, ← pow_add, ← pow_add, ← pow_add]
  congr 1
  ring

/-- Case B: (2a)²·(−d) ≡ 1 (mod f), so (−d/f) = 1. -/
lemma jacobi_neg_d {a d f : ℕ} (hdvd : f ∣ 4 * a ^ 2 * d + 1)
    (hcop : Nat.Coprime (2 * a) f) :
    jacobiSym (-((d : ℕ) : ℤ)) f = 1 := by
  obtain ⟨e, he⟩ := hdvd
  have hcong : ((((2 * a : ℕ)) : ℤ) ^ 2 * (-((d : ℕ) : ℤ)))
      ≡ 1 [ZMOD (((f : ℕ)) : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    have hde : ((((2 * a : ℕ)) : ℤ) ^ 2 * (-((d : ℕ) : ℤ))) - 1
        = -((f : ℕ) : ℤ) * ((e : ℕ) : ℤ) := by
      have he' : ((4 * a ^ 2 * d : ℕ) : ℤ) + 1
          = ((f : ℕ) : ℤ) * ((e : ℕ) : ℤ) := by exact_mod_cast he
      have hmul : ((((2 * a : ℕ)) : ℤ) ^ 2 * (-((d : ℕ) : ℤ))
          = -((4 * a ^ 2 * d : ℕ) : ℤ)) := by push_cast; ring
      rw [hmul]
      linarith
    have h1 : (1 : ℤ) - ((((2 * a : ℕ)) : ℤ) ^ 2 * (-((d : ℕ) : ℤ)))
        = ((f : ℕ) : ℤ) * ((e : ℕ) : ℤ) := by linarith
    rw [h1]
    exact dvd_mul_right _ _
  have hmod : ((((2 * a : ℕ)) : ℤ) ^ 2 * (-((d : ℕ) : ℤ))) % ((f : ℕ) : ℤ)
      = (1 : ℤ) % ((f : ℕ) : ℤ) := hcong
  have hJ := jacobiSym.mod_left' hmod
  have hsq : jacobiSym ((((2 * a : ℕ)) : ℤ) ^ 2) f = 1 := by
    apply jacobiSym.sq_one'
    rw [Int.gcd_natCast_natCast]
    exact hcop
  rw [jacobiSym.mul_left, hsq, jacobiSym.one_left] at hJ
  simpa using hJ

/-- R134 Theorem 2 (T1 two-case): x² ≡ −f (mod 4ad) has no solution
for a,d ≥ 1 and f ∣ 4a²d+1. Hence no T1 class contains a square. -/
theorem t1_two_case {a d f : ℕ} (ha : 1 ≤ a) (hd : 1 ≤ d)
    (hdvd : f ∣ 4 * a ^ 2 * d + 1) :
    ∀ x : ZMod (4 * a * d), x ^ 2 ≠ -((f : ℕ) : ZMod (4 * a * d)) := by
  intro x hx
  have hpos : 0 < 4 * a * d := by positivity
  have : NeZero (4 * a * d) := ⟨hpos.ne'⟩
  have hodd_f : Odd f := odd_f_of_dvd hdvd
  have hcop : Nat.Coprime f (4 * a * d) := coprime_f_4ad hdvd
  have h_int : (x.val : ℤ) ^ 2 ≡ (-(f : ℤ)) [ZMOD (((4 * a * d : ℕ)) : ℤ)] := by
    have hx_eq : x = (((x.val : ℕ)) : ZMod (4 * a * d)) :=
      (ZMod.natCast_zmod_val x).symm
    have h0 : (((x.val : ℕ)) : ZMod (4 * a * d)) ^ 2
        + (((f : ℕ)) : ZMod (4 * a * d)) = 0 := by
      rw [← hx_eq, hx, neg_add_cancel]
    have h0c : (((x.val ^ 2 + f : ℕ)) : ZMod (4 * a * d))
        = (((0 : ℕ)) : ZMod (4 * a * d)) := by
      have h2 : (((x.val ^ 2 + f : ℕ)) : ZMod (4 * a * d))
          = (((x.val : ℕ)) : ZMod (4 * a * d)) ^ 2
            + (((f : ℕ)) : ZMod (4 * a * d)) := by push_cast; ring
      rw [h2]
      simpa using h0
    have hmod : x.val ^ 2 + f ≡ 0 [MOD (4 * a * d)] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp h0c
    have hdvd0 : (4 * a * d) ∣ (x.val ^ 2 + f) := Nat.modEq_zero_iff_dvd.mp hmod
    rw [Int.modEq_iff_dvd]
    have h3 : ((-(f : ℤ)) - (x.val : ℤ) ^ 2) = -(((x.val ^ 2 + f : ℕ)) : ℤ) := by
      push_cast; ring
    rw [h3, dvd_neg]
    exact Int.natCast_dvd_natCast.mpr hdvd0
  have hx_odd : Odd x.val := odd_x_of hodd_f h_int
  have hf4 : f % 4 = 3 := f_mod4 hx_odd h_int
  obtain ⟨t, d₁, hnd, hdt⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (by omega : d ≠ 0) 2 (by norm_num)
  have hodd_d1 : Odd d₁ := by
    rw [← Nat.not_even_iff_odd]
    exact fun hev => hnd (even_iff_two_dvd.mp hev)
  have hdt' : d = d₁ * 2 ^ t := by rw [hdt]; ring
  have hd1_pos : 1 ≤ d₁ :=
    Nat.pos_of_dvd_of_pos ⟨2 ^ t, hdt'⟩ (by omega)
  have hd1_dvd : d₁ ∣ 4 * a * d :=
    ⟨4 * a * 2 ^ t, by rw [hdt]; ring⟩
  rcases (by omega : d₁ = 1 ∨ 1 < d₁) with hd1eq | hd1gt
  · -- Case B: d₁ = 1, so d = 2^t; (−d/f) = 1 but also (−1)^(f/2 + t((f²−1)/8)).
    have hJ1 := jacobi_neg_d hdvd (coprime_2a_f hdvd hodd_f)
    have hd_cast : ((d : ℕ) : ℤ) = (2 : ℤ) ^ t := by
      rw [hdt, hd1eq]; push_cast; ring
    have e1 : (-((d : ℕ) : ℤ)) = (-1) * (2 : ℤ) ^ t := by rw [hd_cast]; ring
    have hJ2 : jacobiSym (-((d : ℕ) : ℤ)) f
        = (-1 : ℤ) ^ (f / 2 + t * ((f ^ 2 - 1) / 8)) := by
      rw [e1, jacobiSym.mul_left, neg_one_jacobi hodd_f, jacobiSym.pow_left,
        jacobi_two hodd_f, ← pow_mul, mul_comm ((f ^ 2 - 1) / 8) t, ← pow_add]
    rw [hJ1] at hJ2
    have hEven : Even (f / 2 + t * ((f ^ 2 - 1) / 8)) :=
      (neg_one_pow_eq_one_iff_even (by norm_num)).mp hJ2.symm
    have hEven2 := Nat.even_iff.mp hEven
    have hBodd : Odd (f / 2) := by rw [Nat.odd_iff]; omega
    have hBodd2 := Nat.odd_iff.mp hBodd
    have hCodd : Odd (t * ((f ^ 2 - 1) / 8)) := by
      rw [Nat.odd_iff]; omega
    obtain ⟨ht1, hf85⟩ := parity_core hCodd hodd_f
    have h8 : (8 : ℕ) ∣ 4 * a * d := eight_dvd_4ad ha ht1 hdt
    have hf87 : f % 8 = 7 := f_mod8 hx_odd h8 h_int
    omega
  · -- Case A: d₁ > 1; (−f/d₁) = 1 but also (−1)^E with E even-forcing.
    have h3z : ((d₁ : ℕ) : ℤ) ∣ ((4 * a * d : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr hd1_dvd
    have h_d1 : (x.val : ℤ) ^ 2 ≡ (-(f : ℤ)) [ZMOD (((d₁ : ℕ)) : ℤ)] :=
      Int.ModEq.of_dvd h3z h_int
    have hcop_x : Nat.Coprime x.val d₁ := coprime_x_d1 hcop hd1_dvd h_int
    have hJ1 : jacobiSym (-(f : ℤ)) d₁ = 1 := by
      have hmod : ((x.val : ℤ) ^ 2) % ((d₁ : ℕ) : ℤ)
          = ((-(f : ℤ))) % ((d₁ : ℕ) : ℤ) := h_d1
      have hsq1 : jacobiSym ((x.val : ℤ) ^ 2) d₁ = 1 := by
        apply jacobiSym.sq_one'
        rw [Int.gcd_natCast_natCast]
        exact hcop_x
      have hJJ := jacobiSym.mod_left' hmod
      rw [hsq1] at hJJ
      exact hJJ.symm
    have hJ2 := jacobi_neg_f hodd_f hodd_d1 hdt hdvd (coprime_a_f hdvd)
    rw [hJ1] at hJ2
    have hEven : Even (d₁ / 2 + (f / 2) * (d₁ / 2) + t * ((f ^ 2 - 1) / 8)
        + f / 2) :=
      (neg_one_pow_eq_one_iff_even (by norm_num)).mp hJ2.symm
    have hAeven : Even (d₁ / 2 + (f / 2) * (d₁ / 2)) := by
      have he1 : Even ((f + 1) / 2) := by rw [Nat.even_iff]; omega
      have he2 : (f + 1) / 2 = (f / 2) + 1 := by
        obtain ⟨k, hk⟩ := hodd_f; omega
      have hE : Even ((d₁ / 2) * ((f + 1) / 2)) := he1.mul_left _
      rw [he2] at hE
      have hrw : (d₁ / 2) * ((f / 2) + 1) = d₁ / 2 + (f / 2) * (d₁ / 2) := by
        ring
      rwa [hrw] at hE
    have hBodd : Odd (f / 2) := by rw [Nat.odd_iff]; omega
    have hEven2 := Nat.even_iff.mp hEven
    have hAeven2 := Nat.even_iff.mp hAeven
    have hBodd2 := Nat.odd_iff.mp hBodd
    have hCodd : Odd (t * ((f ^ 2 - 1) / 8)) := by
      rw [Nat.odd_iff]; omega
    obtain ⟨ht1, hf85⟩ := parity_core hCodd hodd_f
    have h8 : (8 : ℕ) ∣ 4 * a * d := eight_dvd_4ad ha ht1 hdt
    have hf87 : f % 8 = 7 := f_mod8 hx_odd h8 h_int
    omega

end EST1TwoCase
