import Mathlib

open Finset
open Classical

/-!
# R140 |Q| = |S|/2^k CRT count (Round 158, Lean formalization lane)

R140 §2 (dossier): with the CRT decomposition of the unit group over the
prime factors p ≥ 5 of M, the QR condition cuts each `(ZMod p)ˣ` factor
exactly in half — the squaring map on `(ZMod p)ˣ` is 2-to-1 for p ≥ 5 —
independently across p. Hence, with k = #{p | M : p ≥ 5},

  |Q| = ∏_{p} (p−1)/2 = (∏_{p} (p−1)) / 2^k = |S|/2^k.

This module formalizes the counting core in standalone form (the CRT link
to R140's M/S/Q is cited, not re-formalized):

1. `sq_unit_neg_ne`: a₀ ≠ −a₀ in `(ZMod p)ˣ` for prime p ≥ 5.
2. `sq_fiber_finset`: the squaring fiber over a square is exactly {a₀, −a₀}.
3. `card_qr_units`: for prime p ≥ 5, exactly (p−1)/2 nonzero QRs mod p.
4. `qrTupleFinset` + `qr_count_crt`: the product form over a finset of
   primes ≥ 5, via `Finset.pi` / `Finset.card_pi`.
5. `qr_ratio` / `qr_ratio_div`: the 2^k ratio, multiplication and division forms.
6. `qr_core_count`: packaged |Q| = |S|/2^k.
-/

namespace ESQRCoreCount

/-- a₀ ≠ −a₀ in `(ZMod p)ˣ` for prime p ≥ 5 (else 2 ≡ 0 mod p, so p ∣ 2). -/
theorem sq_unit_neg_ne {p : ℕ} [NeZero p] (hp : p.Prime) (h5 : 5 ≤ p) (a₀ : (ZMod p)ˣ) :
    a₀ ≠ -a₀ := by
  letI := Fact.mk hp
  intro h
  have hv : (a₀ : ZMod p) = -(a₀ : ZMod p) := by
    have h2 := congrArg Units.val h
    simpa [Units.val_neg] using h2
  have hv0 : (a₀ : ZMod p) ≠ 0 := by
    intro hz
    have h1 : (1 : ZMod p) = 0 := by
      have hmul : (a₀ : ZMod p) * ((a₀⁻¹ : (ZMod p)ˣ) : ZMod p) = 1 :=
        by exact_mod_cast a₀.mul_inv
      rw [hz, zero_mul] at hmul
      exact hmul.symm
    have hdvd : p ∣ 1 :=
      (ZMod.natCast_eq_zero_iff 1 p).mp (by exact_mod_cast h1)
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have h2le := hp.two_le
    omega
  have h2v : (2 : ZMod p) * (a₀ : ZMod p) = 0 := by
    have hadd : (a₀ : ZMod p) + (a₀ : ZMod p) = 0 := by
      have hnc := neg_add_cancel (a₀ : ZMod p)
      rwa [← hv] at hnc
    rw [two_mul]
    exact hadd
  rcases mul_eq_zero.mp h2v with h2 | h0
  · have hdvd : p ∣ 2 :=
      (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h2)
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · exact hv0 h0

/-- The squaring fiber over a square in `(ZMod p)ˣ` is exactly {a₀, −a₀}. -/
theorem sq_fiber_finset {p : ℕ} [NeZero p] (hp : p.Prime) (h5 : 5 ≤ p) (a₀ : (ZMod p)ˣ) :
    Finset.univ.filter (fun a : (ZMod p)ˣ => a ^ 2 = a₀ ^ 2) = {a₀, -a₀} := by
  letI := Fact.mk hp
  have hne := sq_unit_neg_ne hp h5 a₀
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro ha
    have hfield : (a : ZMod p) ^ 2 = (a₀ : ZMod p) ^ 2 := by
      have hcon := congrArg Units.val ha
      simpa [Units.val_pow_eq_pow_val] using hcon
    have hsub : ((a : ZMod p) - (a₀ : ZMod p)) * ((a : ZMod p) + (a₀ : ZMod p)) = 0 := by
      have e : ((a : ZMod p) - (a₀ : ZMod p)) * ((a : ZMod p) + (a₀ : ZMod p))
          = (a : ZMod p) ^ 2 - (a₀ : ZMod p) ^ 2 := by ring
      rw [e, sub_eq_zero.mpr hfield]
    rcases mul_eq_zero.mp hsub with h | h
    · left
      exact Units.ext (sub_eq_zero.mp h)
    · right
      refine Units.ext ?_
      rw [Units.val_neg]
      exact add_eq_zero_iff_eq_neg.mp h
  · rintro (rfl | rfl)
    · rfl
    · exact neg_pow_two _

/-- For prime p ≥ 5, the nonzero QRs mod p number exactly (p−1)/2. -/
theorem card_qr_units {p : ℕ} [NeZero p] (hp : p.Prime) (h5 : 5 ≤ p) :
    (Finset.univ.filter (fun a : (ZMod p)ˣ => IsSquare a)).card = (p - 1) / 2 := by
  letI := Fact.mk hp
  have himg : Finset.univ.filter (fun a : (ZMod p)ˣ => IsSquare a)
      = Finset.image (fun a : (ZMod p)ˣ => a ^ 2) Finset.univ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨r, hr⟩
      exact ⟨r, by rw [sq, ← hr]⟩
    · rintro ⟨r, hr⟩
      exact ⟨r, by rw [← sq, hr]⟩
  have hfib : ∀ b ∈ Finset.image (fun a : (ZMod p)ˣ => a ^ 2) Finset.univ,
      (Finset.univ.filter (fun a : (ZMod p)ˣ => a ^ 2 = b)).card = 2 := by
    intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨a₀, _, rfl⟩ := hb
    rw [sq_fiber_finset hp h5 a₀, Finset.card_pair (sq_unit_neg_ne hp h5 a₀)]
  have hsum := Finset.card_eq_sum_card_image (fun a : (ZMod p)ˣ => a ^ 2) Finset.univ
  have hsum2 : (Finset.univ : Finset (ZMod p)ˣ).card
      = 2 * (Finset.image (fun a : (ZMod p)ˣ => a ^ 2) Finset.univ).card := by
    calc (Finset.univ : Finset (ZMod p)ˣ).card
        = ∑ _b ∈ Finset.image (fun a : (ZMod p)ˣ => a ^ 2) Finset.univ, 2 := by
          rw [hsum]
          exact Finset.sum_congr rfl (fun b hb => hfib b hb)
      _ = (Finset.image (fun a : (ZMod p)ˣ => a ^ 2) Finset.univ).card * 2 :=
          Finset.sum_const_nat (fun _ _ => rfl)
      _ = 2 * (Finset.image (fun a : (ZMod p)ˣ => a ^ 2) Finset.univ).card := mul_comm _ _
  have hcard : (Finset.univ : Finset (ZMod p)ˣ).card = p - 1 := by
    rw [Finset.card_univ, ZMod.card_units]
  rw [hcard] at hsum2
  have hmul : (Finset.image (fun a : (ZMod p)ˣ => a ^ 2) Finset.univ).card * 2 = p - 1 := by
    rw [mul_comm]; exact hsum2.symm
  have hdiv := Nat.div_eq_of_eq_mul_left (by norm_num : 0 < 2) hmul.symm
  rw [himg]
  exact hdiv.symm

/-- The per-prime QR finset, bundled over all of ℕ (QR units where p ∈ s is
prime, empty elsewhere). The `NeZero` instance is supplied locally from `hs`,
so no global instance is needed. -/
def qrTupleFinset (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) : ∀ p : ℕ, Finset (ZMod p)ˣ :=
  fun p =>
    if h : p ∈ s then
      haveI : NeZero p := ⟨(hs p h).ne_zero⟩
      Finset.univ.filter (fun a : (ZMod p)ˣ => IsSquare a)
    else ∅

/-- CRT count: over a finset of primes ≥ 5, the componentwise-QR tuples
(`Finset.pi` of the per-prime QR finsets) number ∏ (p−1)/2. -/
theorem qr_count_crt (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (h5 : ∀ p ∈ s, 5 ≤ p) :
    (Finset.pi s (qrTupleFinset s hs)).card = ∏ p ∈ s, (p - 1) / 2 := by
  rw [Finset.card_pi]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have : NeZero p := ⟨(hs p hp).ne_zero⟩
  have htp : qrTupleFinset s hs p
      = Finset.univ.filter (fun a : (ZMod p)ˣ => IsSquare a) := by
    simp only [qrTupleFinset, dif_pos hp]
  rw [htp]
  exact card_qr_units (hs p hp) (h5 p hp)

/-- The 2^k ratio, multiplication form. -/
theorem qr_ratio (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (h5 : ∀ p ∈ s, 5 ≤ p) :
    (∏ p ∈ s, (p - 1) / 2) * 2 ^ s.card = ∏ p ∈ s, (p - 1) := by
  have key : ∀ p ∈ s, (p - 1) / 2 * 2 = p - 1 := by
    intro p hp
    obtain ⟨k, hk⟩ := (hs p hp).odd_of_ne_two (by have h := h5 p hp; omega)
    have hev : Even (p - 1) := ⟨k, by omega⟩
    exact Nat.div_mul_cancel (even_iff_two_dvd.mp hev)
  calc (∏ p ∈ s, (p - 1) / 2) * 2 ^ s.card
      = ∏ p ∈ s, ((p - 1) / 2 * 2) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ = ∏ p ∈ s, (p - 1) := Finset.prod_congr rfl (fun p hp => key p hp)

/-- The 2^k ratio, division form: |Q| = |S|/2^k. -/
theorem qr_ratio_div (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (h5 : ∀ p ∈ s, 5 ≤ p) :
    ∏ p ∈ s, (p - 1) / 2 = (∏ p ∈ s, (p - 1)) / 2 ^ s.card := by
  have h := qr_ratio s hs h5
  have hpos : 0 < 2 ^ s.card := by positivity
  have hdiv := Nat.div_eq_of_eq_mul_left hpos h.symm
  exact hdiv.symm

/-- R140 §2 count, packaged: |Q| = |S|/2^k with k = #{primes ≥ 5}. -/
theorem qr_core_count (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (h5 : ∀ p ∈ s, 5 ≤ p) :
    (Finset.pi s (qrTupleFinset s hs)).card = (∏ p ∈ s, (p - 1)) / 2 ^ s.card := by
  rw [qr_count_crt s hs h5, qr_ratio_div s hs h5]

end ESQRCoreCount
