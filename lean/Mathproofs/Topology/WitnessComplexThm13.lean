import Mathlib

/-!
# Witness-complex theorems: Thm 1(a) integrality-iff + Thm 3 full-class (Rounds 126, 130, 141)

Formalizes R126's Theorem 1(a) (Type-II enumeration / integrality iff) and
Theorem 3 (full-class single-shape theorem) from the divisor-conditioned
witness complex W(M) (`~/workspace/math-unsolved/ROUND126_DOSSIER.md`;
paper-grade proofs in `~/workspace/math-unsolved/ROUND130_DOSSIER.md` §3).

Paper setup: fix `(a,c,d) ∈ ℕ³`, `n = Mt+s`, `q = 4acd−1`, `m(t) = (cMt+cs+a)/q`.

**Thm 1(a) kernel** (`t2_integrality_iff`): `m(t) ∈ ℤ` for all `t` iff
`q ∣ (cs+a)` and `q ∣ (cM)` — i.e., with the Euclid step `t2_euclid_step`
(resting on `t2_coprime`: `gcd(4acd−1, c) = 1`), iff `q ∣ (cs+a)` and `q ∣ M`.
Supporting: `t2_mod4` (`q ≡ 3 mod 4`, so `q ∈ Q(M)` in the paper's notation).

**Thm 3 kernel** (`t3_full_class`): given `q+1 = 4acd` and `qm = cn+a`
(all positive), `4/n = 1/(adm) + 1/(nacd) + 1/(ncdm)` in `ℚ`.
The proof is the dossier's polynomial identity: `nc+m+a = m(q+1) = 4acdm`
(`t3_sum_eq`), so the three fractions share the common denominator `n·a·c·d·m`
with numerators `nc`, `m`, `a`. Supporting edge case `t3_class_nonzero`:
`s = 0` would give `q ∣ a`, impossible since `1 ≤ a < q`.

All statements are pure ℕ divisibility + ring; no ES framework dependency.
-/

namespace WitnessComplexThm13

/-- Positivity of `4acd` for positive `a, c, d`. -/
private theorem acd_pos (a c d : ℕ) (ha : 1 ≤ a) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    1 ≤ 4 * a * c * d := by
  have e1 : (0:ℕ) < 4 := by norm_num
  have e2 : (0:ℕ) < a := by omega
  have e3 : (0:ℕ) < c := by omega
  have e4 : (0:ℕ) < d := by omega
  have h := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos e1 e2) e3) e4
  omega

/-- Cast of a positive natural is nonzero in `ℚ`. -/
private theorem cast_ne_zero_of_pos {x : ℕ} (hx : 0 < x) : (x : ℚ) ≠ 0 := by
  exact_mod_cast (ne_of_gt hx)

/-- R126 Thm 1(a), coprimality step: `gcd(4acd−1, c) = 1`.
Any common divisor of `c` and `q = 4acd−1` divides `4acd` and `4acd−1`, hence 1. -/
theorem t2_coprime (a c d q : ℕ) (ha : 1 ≤ a) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hq : q = 4*a*c*d - 1) : Nat.Coprime q c := by
  have key : ∀ k : ℕ, k ∣ c → k ∣ q → k ∣ 1 := by
    intro k hkc hkq
    rw [hq] at hkq
    have h2 : k ∣ 4 * a * c * d := by
      have hck : k ∣ c * (4 * a * d) := dvd_mul_of_dvd_left hkc (4 * a * d)
      rwa [show c * (4 * a * d) = 4 * a * c * d from by ring] at hck
    have hsub := Nat.dvd_sub h2 hkq
    have heq : (4 * a * c * d) - (4 * a * c * d - 1) = 1 := by
      have hp := acd_pos a c d ha hc hd
      omega
    rwa [heq] at hsub
  have hgcd : Nat.gcd c q = 1 := by
    apply Nat.dvd_antisymm
    · exact key _ (Nat.gcd_dvd_left c q) (Nat.gcd_dvd_right c q)
    · exact Nat.one_dvd _
  show Nat.gcd q c = 1
  rw [Nat.gcd_comm]
  exact hgcd

/-- R126 Thm 1(a), Euclid step: `q ∣ cM ↔ q ∣ M` (uses coprimality). -/
theorem t2_euclid_step (a c d M q : ℕ) (ha : 1 ≤ a) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hq : q = 4*a*c*d - 1) : q ∣ c * M ↔ q ∣ M := by
  have hcop : Nat.Coprime q c := t2_coprime a c d q ha hc hd hq
  constructor
  · exact hcop.dvd_of_dvd_mul_left
  · intro h
    exact dvd_mul_of_dvd_right h c

/-- R126 Thm 1(a), the integrality iff (the formalization kernel):
`m(t) = (cMt+cs+a)/q` is integral for all `t` iff `q ∣ (cs+a)` and `q ∣ M`.
Forward: `t = 0` gives `q ∣ (cs+a)`; `m(1)−m(0) = cM/q` gives `q ∣ cM`.
Backward: `m(t) = (cs+a)/q + t·(cM/q)`. -/
theorem t2_integrality_iff (a c d M s q : ℕ) (ha : 1 ≤ a) (hc : 1 ≤ c)
    (hd : 1 ≤ d) (hq : q = 4*a*c*d - 1) :
    (∀ t : ℕ, q ∣ c * M * t + c * s + a) ↔ (q ∣ c * s + a ∧ q ∣ M) := by
  have heuclid := t2_euclid_step a c d M q ha hc hd hq
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    simp only [mul_one, mul_zero, zero_add] at h0 h1
    have hsub := Nat.dvd_sub h1 h0
    have heq : (c * M + c * s + a) - (c * s + a) = c * M := by omega
    rw [heq] at hsub
    exact ⟨h0, heuclid.mp hsub⟩
  · rintro ⟨hcsa, hM⟩ t
    have hMt : q ∣ c * M * t := dvd_mul_of_dvd_left (heuclid.mpr hM) t
    have hassoc : c * M * t + c * s + a = c * M * t + (c * s + a) := by ring
    rw [hassoc]
    exact Nat.dvd_add hMt hcsa

/-- `q = 4acd−1` is `3 mod 4` (so `q ∈ Q(M)` in the paper's notation). -/
theorem t2_mod4 (a c d q : ℕ) (ha : 1 ≤ a) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hq : q = 4*a*c*d - 1) : q % 4 = 3 := by
  have hp := acd_pos a c d ha hc hd
  have hq1 : q + 1 = 4 * a * c * d := by rw [hq]; omega
  obtain ⟨k, hk⟩ : 4 ∣ 4 * a * c * d := ⟨a*c*d, by ring⟩
  have hkq : q + 1 = 4 * k := by rw [hq1]; exact hk
  have hkpos : 1 ≤ k := by
    have h4k : 1 ≤ 4 * k := by rw [← hk]; exact hp
    omega
  omega

/-- R126 Thm 3, the polynomial identity: from `qm = cn+a` and `q+1 = 4acd`,
`nc+m+a = m(q+1) = 4acdm`. This is the common numerator in the `4/n` identity. -/
theorem t3_sum_eq (a c d n m q : ℕ) (hq : q + 1 = 4*a*c*d)
    (hrel : q*m = c*n + a) : n*c + m + a = 4*a*c*d*m := by
  have h1 : n * c + a = q * m := by rw [mul_comm n c]; exact hrel.symm
  calc n * c + m + a = (n * c + a) + m := by ring
    _ = q * m + m := by rw [h1]
    _ = m * (q + 1) := by ring
    _ = m * (4 * a * c * d) := by rw [hq]
    _ = 4 * a * c * d * m := by ring

/-- R126 Thm 3, edge case: `s = 0` cannot satisfy the class condition, since
`q ∣ a` would force `q ≤ a < q`. -/
theorem t3_class_nonzero (a c d q s : ℕ) (ha : 1 ≤ a) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hq : q = 4*a*c*d - 1) (hqs : q ∣ c * s + a) : s ≠ 0 := by
  intro hs
  subst hs
  simp only [mul_zero, zero_add] at hqs
  have hle : q ≤ a := Nat.le_of_dvd (by omega) hqs
  have hlt : a < q := by
    rw [hq]
    have hcd : (1:ℕ) ≤ c * d :=
      Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
    have h1 : 4 * a * 1 ≤ 4 * a * (c * d) :=
      mul_le_mul_of_nonneg_left (by omega) (Nat.zero_le _)
    have hX : 4 * a * c * d = 4 * a * (c * d) := by ring
    omega
  omega

/-- R126 Thm 3 (full-class single-shape theorem): the single parametric shape
covers its class via `4/n = 1/(adm) + 1/(nacd) + 1/(ncdm)`. -/
theorem t3_full_class (a c d n m q : ℕ) (ha : 1 ≤ a) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hq : q + 1 = 4*a*c*d) (hrel : q*m = c*n + a) :
    (4 : ℚ)/(n : ℚ)
      = 1/((a:ℚ)*(d:ℚ)*(m:ℚ)) + 1/((n:ℚ)*(a:ℚ)*(c:ℚ)*(d:ℚ))
        + 1/((n:ℚ)*(c:ℚ)*(d:ℚ)*(m:ℚ)) := by
  have hsum : n * c + m + a = 4 * a * c * d * m := t3_sum_eq a c d n m q hq hrel
  have hN0 : (n:ℚ) ≠ 0 := cast_ne_zero_of_pos (by omega)
  have hD0 : (((n*a*c*d*m : ℕ)):ℚ) ≠ 0 :=
    cast_ne_zero_of_pos (by
      have e1 : 0 < n := by omega
      have e2 : 0 < a := by omega
      have e3 : 0 < c := by omega
      have e4 : 0 < d := by omega
      have e5 : 0 < m := by omega
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos e1 e2) e3) e4) e5)
  have key : (1:ℚ)/((a:ℚ)*(d:ℚ)*(m:ℚ)) + 1/((n:ℚ)*(a:ℚ)*(c:ℚ)*(d:ℚ))
        + 1/((n:ℚ)*(c:ℚ)*(d:ℚ)*(m:ℚ))
      = (((n*c+m+a : ℕ)):ℚ)/(((n*a*c*d*m : ℕ)):ℚ) := by
    have g1 : ((a:ℚ)*(d:ℚ)*(m:ℚ)) ≠ 0 := by
      have h : (((a*d*m : ℕ)):ℚ) ≠ 0 :=
        cast_ne_zero_of_pos
          (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
      rwa [Nat.cast_mul, Nat.cast_mul] at h
    have g2 : ((n:ℚ)*(a:ℚ)*(c:ℚ)*(d:ℚ)) ≠ 0 := by
      have h : (((n*a*c*d : ℕ)):ℚ) ≠ 0 :=
        cast_ne_zero_of_pos
          (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
            (by omega))
      rwa [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul] at h
    have g3 : ((n:ℚ)*(c:ℚ)*(d:ℚ)*(m:ℚ)) ≠ 0 := by
      have h : (((n*c*d*m : ℕ)):ℚ) ≠ 0 :=
        cast_ne_zero_of_pos
          (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
            (by omega))
      rwa [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul] at h
    field_simp
    push_cast
    ring
  rw [key, hsum, div_eq_div_iff hN0 hD0]
  push_cast
  ring

end WitnessComplexThm13
