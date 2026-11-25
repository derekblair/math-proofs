import Mathlib

open Finset
open Classical

/-!
# QR-unit counts and their CRT identification with actual residue classes

The original product-count kernels are preserved: each prime-field unit group
for p ≥ 5 has (p−1)/2 squares, independently across a finite set of primes.
`qr_core_count` retains its original tuple-count statement for compatibility.

The semantic CRT bridge uses the following precise domain:

* `residueModulus s = 24 * ∏ p ∈ s, p`, where s is a finite set of primes ≥ 5;
* `targetResidues s` consists of unit residues congruent to 1 modulo 24;
* `qrResidues s` is the subset with a square root modulo the full modulus.

Thus the fixed 8- and 3-components are both 1. The odd prime part is squarefree.
`natCast_mem_targetResidues` and `natCast_mem_qrResidues` express these sets by
ordinary coprimality and natural-number congruence predicates. `residueCRT`
constructs the CRT ring equivalence, and `targetCRTEquiv` / `qrCRTEquiv`
identify the actual residue sets with the prime-field unit/square-unit tuples.
`qr_residue_count` and `qr_residue_count_finset` then prove |Q| = |S| / 2^k
for these defined sets, with k = s.card, without assuming a bijection or count.

The definition includes M₀ = 2042040 from the nearby q-adic source by taking
s = {5,7,11,13,17}, and refinements by additional distinct primes. It does
not identify an absent external R140 census or a separately filtered frontier
with this explicitly defined target set. No cubic-family exclusion is claimed.
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

/-- Original packaged tuple count, preserved for compatibility. The actual-residue
version is `qr_residue_count` below. -/
theorem qr_core_count (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (h5 : ∀ p ∈ s, 5 ≤ p) :
    (Finset.pi s (qrTupleFinset s hs)).card = (∏ p ∈ s, (p - 1)) / 2 ^ s.card := by
  rw [qr_count_crt s hs h5, qr_ratio_div s hs h5]


/-- Modulus with the fixed `1 mod 24` component and distinct prime factors at least five. -/
def residueModulus (s : Finset ℕ) : ℕ := 24 * ∏ p ∈ s, p

/-- Actual target residues: units congruent to one modulo 24. -/
def targetResidues (s : Finset ℕ) : Set (ZMod (residueModulus s)) :=
  {a | IsUnit a ∧ ZMod.castHom (show 24 ∣ residueModulus s from dvd_mul_right _ _) (ZMod 24) a = 1}

/-- Actual QR core, defined by solvability of a square equation in the full residue ring. -/
def qrResidues (s : Finset ℕ) : Set (ZMod (residueModulus s)) :=
  {a | a ∈ targetResidues s ∧ IsSquare a}

/-- The modulus is positive for any finite set of primes, including the empty set. -/
theorem residueModulus_pos (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    0 < residueModulus s :=
  Nat.mul_pos (by decide) (Finset.prod_pos fun p hp => (hs p hp).pos)

/-- The target is a finite set of genuine residue classes. -/
theorem targetResidues_finite (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (targetResidues s).Finite := by
  have : NeZero (residueModulus s) := ⟨(residueModulus_pos s hs).ne'⟩
  exact Set.toFinite _

/-- The QR core is finite as well. -/
theorem qrResidues_finite (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (qrResidues s).Finite :=
  (targetResidues_finite s hs).subset (fun _ h => h.1)

/-- The residue one always belongs to the QR core, so this is not an empty-set count. -/
theorem one_mem_qrResidues (s : Finset ℕ) :
    (1 : ZMod (residueModulus s)) ∈ qrResidues s := by
  exact ⟨⟨isUnit_one, map_one _⟩, ⟨1, (one_mul 1).symm⟩⟩

/-- The target predicate in ordinary natural-number congruence notation. -/
theorem natCast_mem_targetResidues (s : Finset ℕ) (n : ℕ) :
    (n : ZMod (residueModulus s)) ∈ targetResidues s ↔
      n.Coprime (residueModulus s) ∧ n % 24 = 1 := by
  simp only [targetResidues, Set.mem_ofPred_eq, ZMod.isUnit_iff_coprime, map_natCast]
  rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff']

/-- Membership in the QR core is an ordinary coprimality/congruence predicate,
including an actual natural-number square root modulo the full modulus. -/
theorem natCast_mem_qrResidues (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (n : ℕ) :
    (n : ZMod (residueModulus s)) ∈ qrResidues s ↔
      n.Coprime (residueModulus s) ∧ n % 24 = 1 ∧
        ∃ r : ℕ, r ^ 2 ≡ n [MOD residueModulus s] := by
  have : NeZero (residueModulus s) := ⟨(residueModulus_pos s hs).ne'⟩
  change ((n : ZMod (residueModulus s)) ∈ targetResidues s ∧ IsSquare _) ↔ _
  rw [natCast_mem_targetResidues]
  constructor
  · rintro ⟨⟨hcop, h24⟩, r, hr⟩
    refine ⟨hcop, h24, r.val, ?_⟩
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    rw [Nat.cast_pow, ZMod.natCast_zmod_val, pow_two, ← hr]
  · rintro ⟨hcop, h24, r, hr⟩
    refine ⟨⟨hcop, h24⟩, (r : ZMod (residueModulus s)), ?_⟩
    have he := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hr
    simpa only [Nat.cast_pow, pow_two, Nat.cast_mul] using he.symm

private theorem prime_coprime_24 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    Nat.Coprime 24 p := by
  have h2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
  have h3 : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).mpr (by omega)
  simpa using (h2.pow_left 3).mul_left h3

/-- CRT itself, proved from pairwise coprimality of the supplied distinct primes. -/
noncomputable def residueCRT (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (h5 : ∀ p ∈ s, 5 ≤ p) :
    ZMod (residueModulus s) ≃+* ZMod 24 × ((p : s) → ZMod (p : ℕ)) := by
  have hcop : Nat.Coprime 24 (∏ p ∈ s, p) :=
    Nat.coprime_prod_right_iff.mpr fun p hp => prime_coprime_24 (hs p hp) (h5 p hp)
  have hpair : Pairwise (fun p q : s => Nat.Coprime (p : ℕ) (q : ℕ)) := by
    intro p q hpq
    exact (Nat.coprime_primes (hs p p.property) (hs q q.property)).mpr
      (fun he => hpq (Subtype.ext he))
  let e : ZMod (∏ p ∈ s, p) ≃+* ((p : s) → ZMod (p : ℕ)) :=
    (ZMod.ringEquivCongr (Finset.prod_coe_sort s id).symm).trans
      (ZMod.prodEquivPi (fun p : s => (p : ℕ)) hpair)
  exact (ZMod.chineseRemainder hcop).trans (RingEquiv.prodCongr (RingEquiv.refl _) e)

@[simp] theorem residueCRT_fst (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (h5 : ∀ p ∈ s, 5 ≤ p) (a : ZMod (residueModulus s)) :
    (residueCRT s hs h5 a).1 =
      ZMod.castHom (show 24 ∣ residueModulus s from dvd_mul_right _ _) (ZMod 24) a := by
  exact RingHom.congr_fun (RingHom.ext_zmod
    ((RingHom.fst _ _).comp (residueCRT s hs h5).toRingHom) _) a

@[simp] theorem residueCRT_snd (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (h5 : ∀ p ∈ s, 5 ≤ p) (a : ZMod (residueModulus s)) (p : s) :
    (residueCRT s hs h5 a).2 p =
      ZMod.castHom (show (p : ℕ) ∣ residueModulus s from
        dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem id p.property) _) (ZMod (p : ℕ)) a := by
  exact RingHom.congr_fun (RingHom.ext_zmod
    ((Pi.evalRingHom (fun p : s => ZMod (p : ℕ)) p).comp
      ((RingHom.snd _ _).comp (residueCRT s hs h5).toRingHom)) _) a

private noncomputable def fixedOneUnitEquiv (s : Finset ℕ) :
    {z : ZMod 24 × ((p : s) → ZMod (p : ℕ)) // IsUnit z ∧ z.1 = 1} ≃
      ((p : s) → (ZMod (p : ℕ))ˣ) where
  toFun z p := ((Pi.isUnit_iff.mp (Prod.isUnit_iff.mp z.property.1).2) p).unit
  invFun f := ⟨(1, fun p => (f p : ZMod (p : ℕ))),
    Prod.isUnit_iff.mpr ⟨isUnit_one, Pi.isUnit_iff.mpr (fun p => (f p).isUnit)⟩, rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact z.property.2.symm
    · funext p
      exact IsUnit.unit_spec ((Pi.isUnit_iff.mp (Prod.isUnit_iff.mp z.property.1).2) p)
  right_inv f := by
    funext p
    apply Units.ext
    exact IsUnit.unit_spec _

/-- The target residues are identified with independent prime-field unit choices by CRT. -/
noncomputable def targetCRTEquiv (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (h5 : ∀ p ∈ s, 5 ≤ p) :
    targetResidues s ≃ ((p : s) → (ZMod (p : ℕ))ˣ) :=
  ((residueCRT s hs h5).toEquiv.subtypeEquiv (fun a => by
    change (IsUnit a ∧ ZMod.castHom (show 24 ∣ residueModulus s from dvd_mul_right _ _) (ZMod 24) a = 1) ↔
      (IsUnit (residueCRT s hs h5 a) ∧ (residueCRT s hs h5 a).1 = 1)
    rw [MulEquiv.isUnit_map, residueCRT_fst])).trans (fixedOneUnitEquiv s)

/-- Each coordinate of the identification is the canonical reduction modulo its prime. -/
theorem targetCRTEquiv_coe (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (h5 : ∀ p ∈ s, 5 ≤ p) (a : targetResidues s) (p : s) :
    ((targetCRTEquiv s hs h5 a p : (ZMod (p : ℕ))ˣ) : ZMod (p : ℕ)) =
      (residueCRT s hs h5 a).2 p := by
  exact IsUnit.unit_spec _

private theorem square_unit_iff {R : Type*} [CommMonoid R] (u : Rˣ) :
    IsSquare (u : R) ↔ IsSquare u := by
  constructor
  · rintro ⟨r, hr⟩
    have hrunit : IsUnit r := (IsUnit.mul_iff.mp (hr ▸ u.isUnit)).1
    refine ⟨hrunit.unit, Units.ext ?_⟩
    simpa only [Units.val_mul, IsUnit.unit_spec] using hr
  · exact fun h => h.map (Units.coeHom R)

/-- Full-modulus square solvability is equivalent to square unit choices at every prime.
The fixed 24-coordinate is one and already has a square root. -/
theorem target_isSquare_iff (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (h5 : ∀ p ∈ s, 5 ≤ p) (a : targetResidues s) :
    IsSquare (a : ZMod (residueModulus s)) ↔
      ∀ p : s, IsSquare (targetCRTEquiv s hs h5 a p) := by
  let e := residueCRT s hs h5
  constructor
  · intro ha p
    apply (square_unit_iff _).mp
    rw [targetCRTEquiv_coe]
    exact (ha.map e).map
      ((Pi.evalRingHom (fun p : s => ZMod (p : ℕ)) p).comp (RingHom.snd _ _))
  · intro ha
    choose r hr using ha
    have heq : e a = (1, fun p : s => ((r p : (ZMod (p : ℕ))ˣ) : ZMod (p : ℕ)) * (r p : ZMod (p : ℕ))) := by
      apply Prod.ext
      · exact (residueCRT_fst s hs h5 a).trans a.property.2
      · funext p
        rw [← targetCRTEquiv_coe, hr p]
        rfl
    have hsquare : IsSquare (e a) := ⟨(1, fun p => (r p : ZMod (p : ℕ))), by
      simpa only [Prod.mk_mul_mk, one_mul, Pi.mul_def] using heq⟩
    simpa only [RingEquiv.symm_apply_apply] using hsquare.map e.symm

/-- CRT identification of actual square residue classes with tuples of prime-field square units. -/
noncomputable def qrCRTEquiv (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (h5 : ∀ p ∈ s, 5 ≤ p) :
    qrResidues s ≃ ((p : s) → {u : (ZMod (p : ℕ))ˣ // IsSquare u}) :=
  (Equiv.subtypeSubtypeEquivSubtypeInter (fun a => a ∈ targetResidues s) IsSquare).symm.trans
    (((targetCRTEquiv s hs h5).subtypeEquiv (target_isSquare_iff s hs h5)).trans
      Equiv.subtypePiEquivPi)

/-- Cardinality of actual target residue classes, obtained from the proved CRT equivalence. -/
theorem targetResidues_card (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (h5 : ∀ p ∈ s, 5 ≤ p) :
    Nat.card (targetResidues s) = ∏ p ∈ s, (p - 1) := by
  rw [Nat.card_congr (targetCRTEquiv s hs h5), Nat.card_pi, ← Finset.prod_coe_sort s (fun p : ℕ => p - 1)]
  apply Finset.prod_congr rfl
  intro p _
  have : NeZero (p : ℕ) := ⟨(hs p p.property).ne_zero⟩
  have : Fact (p : ℕ).Prime := ⟨hs p p.property⟩
  rw [Nat.card_eq_fintype_card, ZMod.card_units]

/-- Cardinality of actual square residues in the target set. -/
theorem qrResidues_card (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (h5 : ∀ p ∈ s, 5 ≤ p) :
    Nat.card (qrResidues s) = ∏ p ∈ s, (p - 1) / 2 := by
  rw [Nat.card_congr (qrCRTEquiv s hs h5), Nat.card_pi, ← Finset.prod_coe_sort s (fun p : ℕ => (p - 1) / 2)]
  apply Finset.prod_congr rfl
  intro p _
  have : NeZero (p : ℕ) := ⟨(hs p p.property).ne_zero⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_qr_units (hs p p.property) (h5 p p.property)

/-- `|Q| = |S| / 2^k` for actual residues modulo `24 * ∏ p∈s, p`,
where `S` is precisely the unit residues congruent to one modulo 24 and `Q` is
its full-modulus square subset. No cardinality or bijection is assumed. -/
theorem qr_residue_count (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (h5 : ∀ p ∈ s, 5 ≤ p) :
    Nat.card (qrResidues s) = Nat.card (targetResidues s) / 2 ^ s.card := by
  rw [qrResidues_card s hs h5, targetResidues_card s hs h5, qr_ratio_div s hs h5]

/-- Equivalent finite-set cardinality form for the concrete residue sets. -/
theorem qr_residue_count_finset (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (h5 : ∀ p ∈ s, 5 ≤ p) :
    (qrResidues_finite s hs).toFinset.card =
      (targetResidues_finite s hs).toFinset.card / 2 ^ s.card := by
  simpa only [← Nat.card_eq_card_finite_toFinset] using qr_residue_count s hs h5


end ESQRCoreCount
