import Mathlib

/-!
# T2 prime-square obstruction (Rounds 134, 146)

Formalizes R134's Theorem 1: every Type-II class γ_q of the divisor-conditioned
witness complex W(M) is a quadratic nonresidue mod q.

For q ≡ 3 (mod 4) and a T2 fiber (a, c, d) with 4acd = q+1:

1. **Class-map simplification** (`t2_classmap_simplify`): γ_q = −a·c⁻¹ ≡ −4a²d
   (mod q), since c⁻¹ ≡ 4ad (mod q) from 4acd = q+1 ≡ 1 (mod q). Stated with an
   explicit unit for c to avoid `ZMod`'s gcdA-based `Inv` instance.

2. **Jacobi computation** (`t2_jacobi_neg_one`): the Jacobi symbol
   (−4a²d / q) = −1. Proof: split off (−1)·(4)·(a²)·(d); (−1/q) = −1 since
   q ≡ 3 (mod 4); (4/q) = (a²/q) = 1; and (d/q) = 1 by writing d = 2^t·d₁
   (d₁ odd) — (2/q)^t = 1 via the χ₈ supplementary law with the q ≡ 7 (mod 8)
   / q ≡ 3 (mod 8) case split (in the latter, d | (q+1)/4 odd forces t = 0),
   and (d₁/q) = 1 by quadratic reciprocity plus q ≡ −1 (mod d₁) from
   d₁ | (q+1)/4, which collapses the sign to (−1)^((d₁/2)·((q/2)+1)) = 1
   since (q/2)+1 is even for q ≡ 3 (mod 4).

3. **Nonsquare corollary** (`t2_class_nonsquare`): no x : ZMod q squares to
   −4a²d. Hence no square coprime to q lies in a T2 class — R130's prime-square
   obstruction, strengthened to all squares, as the Lean-checked kernel.

This is the staged follow-up named by the R141 brief ("the cleaner
formalization"); it unblocks R140's QR-core theorem for a later lane.
-/

namespace ESPrimeSquareT2

/-- Coprimality from the fiber equation: any divisor of both x and q (with
x ∣ 4acd) divides 4acd − q = 1. -/
lemma nat_coprime_of_factor {q a c d x : ℕ} (hfac : 4 * a * c * d = q + 1)
    (hx : x ∣ 4 * a * c * d) : Nat.Coprime x q := by
  have hg : Nat.gcd x q ∣ 1 := by
    have h1 : Nat.gcd x q ∣ 4 * a * c * d := dvd_trans (Nat.gcd_dvd_left x q) hx
    have h2 : Nat.gcd x q ∣ q := Nat.gcd_dvd_right x q
    have h3 : Nat.gcd x q ∣ (4 * a * c * d - q) := Nat.dvd_sub h1 h2
    have h4 : 4 * a * c * d - q = 1 := by omega
    rwa [h4] at h3
  have h5 : Nat.gcd x q = 1 := Nat.dvd_one.mp hg
  show Nat.gcd x q = 1
  exact h5

/-- Key Jacobi computation: (d/q) = 1 for d ∣ (q+1)/4, q ≡ 3 (mod 4). -/
lemma jacobiSym_d_eq_one {q d : ℕ} (hq : Odd q) (hq4 : q % 4 = 3)
    (hd : 1 ≤ d) (hdvd4 : d ∣ (q + 1) / 4) :
    jacobiSym ((d : ℕ) : ℤ) q = 1 := by
  obtain ⟨t, d₁, hnd, hdt⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (by omega : d ≠ 0) 2 (by norm_num)
  have hodd1 : Odd d₁ := by
    rw [← Nat.not_even_iff_odd]
    exact fun hev => hnd (even_iff_two_dvd.mp hev)
  have hdvd1 : d₁ ∣ q + 1 := by
    have h1 : d₁ ∣ d := ⟨2 ^ t, by rw [hdt]; ring⟩
    have h2 : d ∣ q + 1 := by
      refine dvd_trans hdvd4 ⟨4, ?_⟩
      have hdm := Nat.div_add_mod (q + 1) 4
      have h4d : 4 ∣ q + 1 := by omega
      omega
    exact dvd_trans h1 h2
  have hcast : ((d : ℕ) : ℤ) = (2 : ℤ) ^ t * ((d₁ : ℕ) : ℤ) := by
    rw [hdt]; push_cast; ring
  rw [hcast, jacobiSym.mul_left, jacobiSym.pow_left]
  have h2t : jacobiSym (2 : ℤ) q ^ t = 1 := by
    rcases (by omega : q % 8 = 3 ∨ q % 8 = 7) with hq8 | hq8
    · -- q ≡ 3 (mod 8): (q+1)/4 is odd, and d ∣ (q+1)/4, so d is odd, so t = 0.
      have hodd14 : Odd ((q + 1) / 4) := by
        have hj := Nat.div_add_mod q 8
        rw [hq8] at hj
        exact ⟨q / 8, by omega⟩
      have ht0 : t = 0 := by
        by_contra ht
        have h2d : 2 ∣ d := by
          rw [hdt]
          exact dvd_trans (dvd_pow_self 2 ht) (dvd_mul_right _ _)
        have h2q : 2 ∣ (q + 1) / 4 := dvd_trans h2d hdvd4
        obtain ⟨k, hk⟩ := hodd14
        omega
      rw [ht0, pow_zero]
    · -- q ≡ 7 (mod 8): (2/q) = χ₈ q = 1.
      have hJ2 : jacobiSym (2 : ℤ) q = 1 := by
        rw [jacobiSym.at_two hq, ZMod.χ₈_nat_eq_if_mod_eight,
          ite_eq_right (by omega : ¬ q % 2 = 0),
          ite_eq_left (by omega : q % 8 = 1 ∨ q % 8 = 7)]
      rw [hJ2, one_pow]
  have hd1 : jacobiSym ((d₁ : ℕ) : ℤ) q = 1 := by
    rw [jacobiSym.quadratic_reciprocity hodd1 hq]
    have hJq : jacobiSym ((q : ℕ) : ℤ) d₁ = (-1 : ℤ) ^ (d₁ / 2) := by
      have hmod : ((q : ℕ) : ℤ) % ((d₁ : ℕ) : ℤ) = (-1 : ℤ) % ((d₁ : ℕ) : ℤ) := by
        obtain ⟨M, hM⟩ := hdvd1
        have hcast : ((q : ℕ) : ℤ) + 1 = ((d₁ : ℕ) : ℤ) * ((M : ℕ) : ℤ) := by
          have h2 : ((((q + 1 : ℕ)) : ℤ)) = ((((d₁ * M : ℕ)) : ℤ)) := by rw [hM]
          calc ((q : ℕ) : ℤ) + 1 = ((((q + 1 : ℕ)) : ℤ)) := by push_cast; ring
            _ = ((((d₁ * M : ℕ)) : ℤ)) := h2
            _ = ((d₁ : ℕ) : ℤ) * ((M : ℕ) : ℤ) := by push_cast; ring
        have hdvd' : ((d₁ : ℕ) : ℤ) ∣ ((q : ℕ) : ℤ) + 1 := by
          rw [hcast]; exact dvd_mul_right _ _
        rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
        have e : ((q : ℕ) : ℤ) - (-1) = ((q : ℕ) : ℤ) + 1 := by ring
        rw [e]
        exact Int.emod_eq_zero_of_dvd hdvd'
      rw [jacobiSym.mod_left' hmod, jacobiSym.at_neg_one hodd1]
      exact ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hodd1)
    rw [hJq, ← pow_add]
    have heven : Even (d₁ / 2 * (q / 2) + d₁ / 2) := by
      have hq2 : Even (q / 2 + 1) := by
        have hj := Nat.div_add_mod q 4
        rw [hq4] at hj
        exact ⟨q / 4 + 1, by omega⟩
      have hrw : d₁ / 2 * (q / 2) + d₁ / 2 = d₁ / 2 * (q / 2 + 1) := by ring
      rw [hrw]
      exact hq2.mul_left _
    exact Even.neg_one_pow heven
  rw [h2t, hd1, mul_one]

/-- R134 Theorem 1, class-map simplification: γ_q = −a·c⁻¹ ≡ −4a²d (mod q),
since c·(4ad) = 4acd = q+1 ≡ 1 (mod q). The unit hypothesis is c's unit
witness (gcd(c,q) = 1 by `nat_coprime_of_factor`). -/
lemma t2_classmap_simplify {q a c d : ℕ}
    (hfac : 4 * a * c * d = q + 1)
    (u : (ZMod q)ˣ) (hu : (u : ZMod q) = (c : ZMod q)) :
    -((a : ZMod q)) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)
      = -((((4 * a ^ 2 * d : ℕ))) : ZMod q) := by
  have h1 : (c : ZMod q) * ((((4 * a * d : ℕ))) : ZMod q) = 1 := by
    have hcast : ((((4 * a * c * d : ℕ))) : ZMod q) = 1 := by
      rw [hfac, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add]
    have h2 : (c : ZMod q) * ((((4 * a * d : ℕ))) : ZMod q)
        = ((((4 * a * c * d : ℕ))) : ZMod q) := by
      push_cast; ring
    rw [h2, hcast]
  have huv : (u : ZMod q) * ((((4 * a * d : ℕ))) : ZMod q) = 1 := by
    rw [hu]; exact h1
  have hvinv : ((((4 * a * d : ℕ))) : ZMod q) = ((u⁻¹ : (ZMod q)ˣ) : ZMod q) :=
    Units.eq_inv_of_mul_eq_one_left huv
  rw [← hvinv]
  push_cast
  ring

/-- R134 Theorem 1 (Jacobi form): for q ≡ 3 (mod 4) and a T2 fiber
4acd = q+1, the Jacobi symbol (−4a²d / q) = −1. -/
theorem t2_jacobi_neg_one {q a c d : ℕ}
    (hq4 : q % 4 = 3) (_ha : 1 ≤ a) (_hc : 1 ≤ c) (hd : 1 ≤ d)
    (hfac : 4 * a * c * d = q + 1) :
    jacobiSym (-4 * (a : ℤ) ^ 2 * (d : ℤ)) q = -1 := by
  have hq : Odd q := Nat.odd_iff.mpr (by omega)
  have hcop_a : Nat.Coprime a q := nat_coprime_of_factor hfac ⟨4 * c * d, by ring⟩
  have hJa2 : jacobiSym ((a : ℤ) ^ 2) q = 1 := by
    apply jacobiSym.sq_one'
    rw [Int.gcd_natCast_natCast]
    exact hcop_a
  have hdvd4 : d ∣ (q + 1) / 4 := by
    have hq1 : q + 1 = 4 * (a * c * d) := by rw [← hfac]; ring
    have hdiv : (q + 1) / 4 = a * c * d := by omega
    rw [hdiv]; exact ⟨a * c, by ring⟩
  have hJd : jacobiSym ((d : ℕ) : ℤ) q = 1 := jacobiSym_d_eq_one hq hq4 hd hdvd4
  have hsplit : (-4 * (a : ℤ) ^ 2 * (d : ℤ)) = (-1) * (4 * ((a : ℤ) ^ 2) * (d : ℤ)) := by
    ring
  rw [hsplit, jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.mul_left,
    jacobiSym.at_neg_one hq, ZMod.χ₄_nat_three_mod_four hq4,
    jacobiSym.at_four hq, hJa2, hJd]
  ring

/-- R134 Theorem 1 (nonsquare form): no x : ZMod q squares to the T2 class
residue −4a²d. Hence no square coprime to q lies in a T2 class — R130's
prime-square obstruction, strengthened to all squares. -/
theorem t2_class_nonsquare {q a c d : ℕ}
    (hq4 : q % 4 = 3) (_ha : 1 ≤ a) (_hc : 1 ≤ c) (hd : 1 ≤ d)
    (hfac : 4 * a * c * d = q + 1) :
    ¬ IsSquare (((-4 * (a : ℤ) ^ 2 * (d : ℤ)) : ℤ) : ZMod q) :=
  ZMod.nonsquare_of_jacobiSym_eq_neg_one (t2_jacobi_neg_one hq4 _ha _hc hd hfac)

end ESPrimeSquareT2
