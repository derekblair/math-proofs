/-
  ESFiberCompat.lean — R185 Fiber-Compatibility Theorem kernel: sharp inverse-closure characterization for prime-power projections (A_map involution, Hensel digit sets, pair-closure).

  Paper: papers/fiber-compatibility-composite-suppression-October-11-2026/
  Status: [PROVED] — fiber_compat_pair_iff, fiber_compat_saturated, fiber_compat_card, forced_digit (+ unit/digit API)
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); machine-checked on bakkie (R190), `lake build` exit 0, zero sorrys, axioms standard-only [propext, Classical.choice, Quot.sound].
-/

import Mathlib

/-!
# R185 Fiber-Compatibility Theorem (Rounds 190/194, Lean formalization lane)

R185 §1 (dossier `~/workspace/math-unsolved/ROUND185_DOSSIER.md`): the sharp
characterization of inverse-closure for prime-power projections.

Setup: `P ⊂ ℤ` finite, `m = p^e`, `π` = projection mod `m`. For each base
class `r mod p^{e-1}` the Hensel digit set is
`S_r = { u ∈ {0,…,p-1} : r + p^{e-1}·u ∈ π(P) }`.
All parent projections here are units, so the unit-only statement covers
everything.

**Theorem (R185 §1).** `π(P)` is inverse-closed ⟺ for every unit base class
`r mod p^{e-1}`, with `r* = r⁻¹ mod p^{e-1}`: `S_{r*} = A_r(S_r)`, where
`A_r(u) = (−u(r*)² − k·r*) mod p`, `k = (rr*−1)/p^{e−1}`.

This module formalizes the elementary kernel (Bézout + affine bijections on
`ZMod p`), in standalone form (imports only Mathlib):

1. `A_map`: the forced digit map `u ↦ −u·s² − k·s` on `ZMod p`
   (`s` plays the role of `r*`, `k` the shared quotient).
2. `A_map_injective` / `A_equiv`: the map is an affine bijection
   (slope `−s²` a unit); explicit two-sided inverse.
3. `A_map_invol`: `A_{r*} ∘ A_r = id` (R185 verified this computationally;
   here it is proved: `linear_combination` certificate).
4. `forced_digit`: the Bézout heart — if `(r + p^{e-1}u)(s + p^{e-1}v) ≡ 1`
   mod `p^e` with `rs = 1 + p^{e-1}k`, then `v ≡ −u·s² − k·s` mod `p`.
   The inverse's digit is FORCED to be `A_r(u)`.
5. `fiber_compat_pair_iff`: the pair-level iff — inverse-closure at one
   inverse pair (digit form) ⟺ `S_{r*} = Finset.image A_r S_r`. The `(⇒)` direction
   is the dossier's card argument via the involution; `(⇐)` is immediate.
6. `fiber_compat_saturated` (Corollary 1): full fibers are sufficient.
7. `fiber_compat_card` (Corollary 2): compatibility forces equal fiber
   sizes — the counting refutation.
8. `fiber_compat_partial_closed` (Corollary 3, m = 8 witness): the digit
   set `{0}` is fixed by `A_1`, so a partial fiber can be closed.
9. `FiberCompatLift.fiber_compat_iff` (R194): the full `π(P)` lift-set
   packaging — `P` inverse-closed ⟺ digit-compatibility
   `S_{r⁻¹} = Finset.image A_r S_r` at every unit base class `r`.
   Promotes R185's theorem [PROVED*] → [PROVED].

Cited, not re-formalized: the empirical iff on the 10 prime powers
[COMPUTED ×2] and the per-prime archaeology [COMPUTED] — R185 §§2–5.

Preprint protocol note: R185 has no preprint yet, so there is no paper
slug for the module header to cite; when the preprint is written it must
reference this module and `fiber_compat_pair_iff` by name.
-/

variable {p : ℕ} [Fact p.Prime]

/-- The forced Hensel digit map: `A_r(u) = −u·(r*)² − k·r*` on digits mod `p`.
Here `s` plays the role of `r*` (the inverse of the base class `r`), and `k`
is the shared quotient `(rr* − 1)/p^{e−1}` (symmetric in `r, r*`). -/
def A_map (s k : ZMod p) : ZMod p → ZMod p := fun u => -(u * s^2) - k * s

/-- The digit map is injective: an affine map with unit slope `−s²`. -/
theorem A_map_injective {s k : ZMod p} (hs : s ≠ 0) :
    Function.Injective (A_map s k) := by
  intro a b h
  simp only [A_map] at h
  have h2 : a * s^2 = b * s^2 := by linear_combination -h
  exact mul_right_cancel₀ (pow_ne_zero 2 hs) h2

/-- The digit map is an explicit equivalence (two-sided inverse written out). -/
def A_equiv (s k : ZMod p) (hs : s ≠ 0) : ZMod p ≃ ZMod p where
  toFun := A_map s k
  invFun := fun v => (v + k * s) * (-(s^2))⁻¹
  left_inv := fun u => by
    have h1 : (s^2 : ZMod p) ≠ 0 := pow_ne_zero 2 hs
    have hm : (-(s^2) : ZMod p) * (-(s^2))⁻¹ = 1 :=
      mul_inv_cancel₀ (neg_ne_zero.mpr h1)
    show ((-(u * s^2) - k * s) + k * s) * (-(s^2))⁻¹ = u
    have e1 : (-(u * s^2) - k * s) + k * s = -(u * s^2) := by ring
    have e2 : (-(u * s^2) : ZMod p) = u * (-(s^2)) := by ring
    rw [e1, e2, mul_assoc, hm, mul_one]
  right_inv := fun v => by
    have h1 : (s^2 : ZMod p) ≠ 0 := pow_ne_zero 2 hs
    have hm : (-(s^2) : ZMod p)⁻¹ * s^2 = -1 := by
      have h0 : (-(s^2) : ZMod p) ≠ 0 := neg_ne_zero.mpr h1
      have e : (s^2 : ZMod p) = -(-(s^2)) := by rw [neg_neg]
      nth_rewrite 2 [e]
      rw [mul_neg, inv_mul_cancel₀ h0]
    show -(((v + k * s) * (-(s^2))⁻¹) * s^2) - k * s = v
    have e1 : ((v + k * s) * (-(s^2))⁻¹) * s^2 = -((v + k * s)) := by
      rw [mul_assoc, hm, mul_neg, mul_one]
    rw [e1]
    ring

/-- `A_{r*} ∘ A_r = id`: applying the digit map twice (with the shared `k`
and inverse slopes `t·s = 1`) returns the digit. R185 verified this
computationally on all 10 moduli; here it is proved. -/
theorem A_map_invol {s t k : ZMod p} (hts : t * s = 1) (u : ZMod p) :
    A_map s k (A_map t k u) = u := by
  have hts2 : t^2 * s^2 = 1 := by rw [← mul_pow, hts, one_pow]
  simp only [A_map]
  linear_combination u * hts2 + k * s * hts

/-- Symmetric form: `A_r ∘ A_{r*} = id`. -/
theorem A_map_invol_symm {s t k : ZMod p} (hts : t * s = 1) (u : ZMod p) :
    A_map t k (A_map s k u) = u :=
  A_map_invol (by rw [mul_comm]; exact hts) u

/-- Integer Bézout core of the forced-digit computation: from the lifted
inverse equation, cancelling the common factor `q = p^{e-1}` and multiplying
by `s` (using `rs ≡ 1` mod `p`) forces `p ∣ v + u·s² + k·s`. -/
theorem forced_digit_aux {e : ℕ} {q : ℤ} (he : 2 ≤ e)
    (hq : q = (p : ℤ) ^ (e - 1)) (hp0 : (p : ℤ) ≠ 0)
    {r s k u v t : ℤ} (hrs : r * s = 1 + q * k)
    (hinv : (r + q * u) * (s + q * v) = 1 + (p : ℤ) ^ e * t) :
    (p : ℤ) ∣ (v + u * s ^ 2 + k * s) := by
  have hq0 : q ≠ 0 := by rw [hq]; exact pow_ne_zero _ hp0
  have hexpand : (r + q * u) * (s + q * v)
      = 1 + q * k + q * (u * s + r * v) + q ^ 2 * (u * v) := by
    have e1 : (r + q * u) * (s + q * v)
        = r * s + q * (u * s + r * v) + q ^ 2 * (u * v) := by ring
    rw [e1, hrs]
  have hpe : (p : ℤ) ^ e = q * p := by
    rw [hq]
    have he1 : e = (e - 1) + 1 := by omega
    conv_lhs => rw [he1]
    rw [pow_succ]
  rw [hpe] at hinv
  have hcancel : k + (u * s + r * v) + q * (u * v) = p * t := by
    have h := hinv
    rw [hexpand] at h
    have h2 : q * (k + (u * s + r * v) + q * (u * v)) = q * (p * t) := by
      linear_combination h
    exact mul_left_cancel₀ hq0 h2
  have hmul : (k + (u * s + r * v) + q * (u * v)) * s = (p * t) * s := by
    rw [hcancel]
  have hrvs : r * v * s = v + v * (q * k) := by
    have e3 : r * v * s = v * (r * s) := by ring
    rw [e3, hrs]; ring
  have key : v + u * s ^ 2 + k * s = p * (t * s) - q * (v * k + s * u * v) := by
    have h3 : (k + (u * s + r * v) + q * (u * v)) * s
        = k * s + u * s ^ 2 + r * v * s + q * (u * v) * s := by ring
    rw [h3, hrvs] at hmul
    linear_combination hmul
  have hq2 : q = p * (p : ℤ) ^ (e - 2) := by
    rw [hq]
    have he2 : e - 1 = (e - 2) + 1 := by omega
    rw [he2, pow_succ]; ring
  rw [hq2] at key
  exact ⟨t * s - (p : ℤ) ^ (e - 2) * (v * k + s * u * v), by linear_combination key⟩

/-- The inverse's Hensel digit is FORCED: if `x = r + p^{e-1}·u` is a unit
lift with inverse `y = s + p^{e-1}·v` mod `p^e` (where `s` inverts `r` and
`rs = 1 + p^{e-1}·k`), then `v = A_r(u) = −u·s² − k·s` mod `p`. -/
theorem forced_digit {e : ℕ} (hp : p.Prime) (he : 2 ≤ e)
    {r s k u v : ℤ} (hrs : r * s = 1 + (p : ℤ) ^ (e - 1) * k)
    (hinv : (r + (p : ℤ) ^ (e - 1) * u) * (s + (p : ℤ) ^ (e - 1) * v)
      ≡ 1 [ZMOD (p : ℤ) ^ e]) :
    v ≡ -(u * s ^ 2) - k * s [ZMOD (p : ℤ)] := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [Int.modEq_iff_dvd] at hinv
  obtain ⟨t, ht⟩ := hinv
  have hinv' : (r + (p : ℤ) ^ (e - 1) * u) * (s + (p : ℤ) ^ (e - 1) * v)
      = 1 + (p : ℤ) ^ e * (-t) := by
    linear_combination -ht
  have hdvd := forced_digit_aux he rfl hp0 hrs hinv'
  rw [Int.modEq_iff_dvd]
  have e4 : (-(u * s ^ 2) - k * s) - v = -(v + u * s ^ 2 + k * s) := by ring
  rw [e4]
  exact dvd_neg.mpr hdvd

/-- Inverse-closure at one inverse pair, in digit form: the A-map sends the
digit set of the base class into the digit set of the inverse class. -/
def PairClosed (s k : ZMod p) (D D' : Finset (ZMod p)) : Prop :=
  ∀ u ∈ D, A_map s k u ∈ D'

/-- The pair-level Fiber-Compatibility iff (R185 Theorem, kernel form):
inverse-closure at one inverse pair (digit form, both directions — the
dossier's `(⇒)` applies closure to `r*` and uses the involution for the
card argument) holds exactly when `S_{r*} = Finset.image A_r S_r`. -/
theorem fiber_compat_pair_iff {s t k : ZMod p} (hts : t * s = 1) (hs : s ≠ 0)
    (D D' : Finset (ZMod p)) :
    (PairClosed s k D D' ∧ PairClosed t k D' D) ↔ D' = Finset.image (A_map s k) D := by
  constructor
  · rintro ⟨hD, hD'⟩
    simp only [PairClosed] at hD hD'
    have hinj : Function.Injective (A_map s k) := A_map_injective hs
    have ht0 : t ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hts
      exact zero_ne_one hts
    have hinj' : Function.Injective (A_map t k) := A_map_injective ht0
    have himg : Finset.image (A_map s k) D ⊆ D' := by
      intro v hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      exact hD u hu
    have himg' : Finset.image (A_map t k) D' ⊆ D := by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact hD' w hw
    have hcc : D.card = D'.card := by
      have h1 : (Finset.image (A_map s k) D).card ≤ D'.card := Finset.card_le_card himg
      have h2 : (Finset.image (A_map t k) D').card ≤ D.card := Finset.card_le_card himg'
      rw [Finset.card_image_of_injective _ hinj] at h1
      rw [Finset.card_image_of_injective _ hinj'] at h2
      omega
    have hfin : D'.card ≤ (Finset.image (A_map s k) D).card := by
      rw [Finset.card_image_of_injective _ hinj]
      omega
    exact (Finset.eq_of_subset_of_card_le himg hfin).symm
  · intro h
    constructor
    · intro u hu
      rw [h]
      exact Finset.mem_image_of_mem _ hu
    · intro v hv
      rw [h] at hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      rw [A_map_invol_symm hts]
      exact hu

/-- Corollary 1 (R185): saturation is sufficient — full fibers are
digit-compatible, since the A-map is a bijection. -/
theorem fiber_compat_saturated {s t k : ZMod p} (_hts : t * s = 1) (hs : s ≠ 0) :
    (Finset.univ : Finset (ZMod p)) = Finset.image (A_map s k) Finset.univ := by
  have hsurj : Function.Surjective (A_map s k) := by
    intro v
    obtain ⟨u, hu⟩ := (A_equiv s k hs).surjective v
    exact ⟨u, hu⟩
  symm
  apply Finset.eq_univ_of_forall
  intro v
  obtain ⟨u, hu⟩ := hsurj v
  rw [← hu]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

/-- Corollary 2 (R185): compatibility forces equal fiber sizes — the
counting refutation: `|S_r| ≠ |S_{r*}|` makes closure impossible. -/
theorem fiber_compat_card {s k : ZMod p} (hs : s ≠ 0)
    (D D' : Finset (ZMod p)) (h : D' = Finset.image (A_map s k) D) :
    D.card = D'.card := by
  rw [h, Finset.card_image_of_injective _ (A_map_injective hs)]

/-- Corollary 3 (R185), the m = 8 witness: the partial digit set `{0}` is
fixed by `A_1` (here `p = 2`, `r = r* = 1`, `k = (1·1−1)/4 = 0`), so an
unsaturated fiber can still be inverse-closed. -/
theorem fiber_compat_partial_closed :
    Finset.image (A_map (1 : ZMod 2) 0) ({0} : Finset (ZMod 2)) = {0} := by
  decide


/-!
## R194: the π(P) lift-set packaging (Round 194, Lean formalization lane)

R190 formalized the kernel (digit map, forced digit, pair-level iff,
Corollaries 1–3) and left the lift-set packaging [PROVED*]: from a finite
set `P : Finset (ZMod p^e)` of units, build the Hensel digit sets
`S_r = { u : r + p^{e-1}·u ∈ P }` and prove the full iff — `P`
inverse-closed ⟺ every unit base class `r` satisfies
`S_{r⁻¹} = Finset.image A_r S_r`.

This section formalizes that packaging, promoting R185's full
Fiber-Compatibility Theorem [PROVED*] → [PROVED].

Note on inverses: `ZMod n` carries its own Bézout-based `ZMod.instInv`
(`ZMod.inv`, via `Nat.gcdA`), not the `DivisionMonoid` one, so the
general inverse lemmas do not apply. We build the small API we need
(`unit_mul_inv`, `unit_inv_eq_of_mul_eq_one`, `unit_inv_isUnit`,
`unit_inv_inv`) from `ZMod.mul_inv_eq_gcd`.
-/

namespace FiberCompatLift

variable {e : ℕ}

/-- For a unit, `a * a⁻¹ = 1` (ZMod's Bézout inverse). -/
theorem unit_mul_inv {n : ℕ} [NeZero n] {a : ZMod n} (ha : IsUnit a) :
    a * a⁻¹ = 1 := by
  rw [ZMod.mul_inv_eq_gcd]
  have e : a = (((a.val : ℕ)) : ZMod n) := (ZMod.natCast_zmod_val a).symm
  have hcop : a.val.Coprime n := (ZMod.isUnit_iff_coprime _ _).mp (e ▸ ha)
  have hgcd : Nat.gcd a.val n = 1 := hcop.gcd_eq_one
  rw [hgcd, Nat.cast_one]

/-- Uniqueness of the unit inverse: `a * b = 1` forces `b = a⁻¹`. -/
theorem unit_inv_eq_of_mul_eq_one {n : ℕ} [NeZero n] {a b : ZMod n}
    (ha : IsUnit a) (h : a * b = 1) : b = a⁻¹ := by
  have h1 : a⁻¹ * a = 1 := by rw [mul_comm]; exact unit_mul_inv ha
  calc b = 1 * b := (one_mul b).symm
    _ = (a⁻¹ * a) * b := by rw [h1]
    _ = a⁻¹ * (a * b) := by rw [mul_assoc]
    _ = a⁻¹ * 1 := by rw [h]
    _ = a⁻¹ := mul_one _

/-- The inverse of a unit is a unit. -/
theorem unit_inv_isUnit {n : ℕ} [NeZero n] {a : ZMod n} (ha : IsUnit a) :
    IsUnit (a⁻¹) := by
  have ha0 := ha
  obtain ⟨u, hu⟩ := ha0
  have h1 : a * ((u⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := by
    rw [← hu]
    exact Units.mul_inv u
  have h2 : a⁻¹ = ((u⁻¹ : (ZMod n)ˣ) : ZMod n) :=
    (unit_inv_eq_of_mul_eq_one ha h1).symm
  rw [h2]
  exact (u⁻¹).isUnit

/-- Double inverse for units: `a⁻¹⁻¹ = a`. -/
theorem unit_inv_inv {n : ℕ} [NeZero n] {a : ZMod n} (ha : IsUnit a) :
    a⁻¹⁻¹ = a := by
  have h1 : a⁻¹ * a = 1 := by rw [mul_comm]; exact unit_mul_inv ha
  exact (unit_inv_eq_of_mul_eq_one (unit_inv_isUnit ha) h1).symm

/-- The natural projection `ZMod p^e →+* ZMod p^(e-1)` (reduction mod `p^{e-1}`). -/
def proj (e : ℕ) : ZMod (p^e) →+* ZMod (p^(e-1)) :=
  ZMod.castHom (pow_dvd_pow p (Nat.sub_le e 1)) (ZMod (p^(e-1)))

/-- The top Hensel digit of `x : ZMod p^e`: the `u` with `x = r + p^{e-1}·u`. -/
def hdigit (e : ℕ) (x : ZMod (p^e)) : ZMod p :=
  ((x.val / p^(e-1) : ℕ) : ZMod p)

/-- The Hensel digit set `S_r = { u : r + p^{e-1}·u ∈ P }` of a base class `r`. -/
def digitSet (e : ℕ) (P : Finset (ZMod (p^e))) (r : ZMod (p^(e-1))) : Finset (ZMod p) :=
  (P.filter (fun x => proj e x = r)).image (hdigit e)

/-- The shared quotient `k_r = (r.val·(r⁻¹).val − 1)/p^{e-1}` as a natural
number; symmetric in `r, r⁻¹`, matching the kernel's shared `k`. -/
def Kquot (e : ℕ) (r : ZMod (p^(e-1))) : ℕ :=
  (r.val * (r⁻¹).val - 1) / p^(e-1)

/-- The projection reads off the low digits: `(proj e x).val = x.val % p^{e-1}`. -/
theorem proj_val (x : ZMod (p^e)) : (proj e x).val = x.val % p^(e-1) := by
  haveI : NeZero (p^e) := ⟨pow_ne_zero _ (Fact.out : p.Prime).pos.ne'⟩
  haveI : NeZero (p^(e-1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).pos.ne'⟩
  unfold proj
  rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.val_natCast]

/-- Digit expansion: `x` is rebuilt from its base class and its top digit. -/
theorem hdigit_recon (he : 2 ≤ e) (x : ZMod (p^e)) :
    x = (((proj e x).val : ℕ) : ZMod (p^e))
      + (((p^(e-1) : ℕ)) : ZMod (p^e)) * ((((hdigit e x).val : ℕ)) : ZMod (p^e)) := by
  haveI : NeZero (p^e) := ⟨pow_ne_zero _ (Fact.out : p.Prime).pos.ne'⟩
  have h1 : (proj e x).val = x.val % p^(e-1) := proj_val x
  have hdiv : x.val / p^(e-1) < p := by
    have hpe : p^e = p^(e-1) * p := by
      conv_lhs => rw [show e = (e-1) + 1 from by omega, pow_succ]
    have hlt : x.val < p^(e-1) * p := by
      have h1x := ZMod.val_lt x
      omega
    by_contra hcon
    have hle : p ≤ x.val / p^(e-1) := not_lt.mp hcon
    have hda := Nat.div_add_mod x.val (p^(e-1))
    have key : p^(e-1) * p ≤ x.val := by
      have hle2 : p^(e-1) * p ≤ p^(e-1) * (x.val / p^(e-1)) :=
        Nat.mul_le_mul le_rfl hle
      omega
    omega
  have h2 : (hdigit e x).val = x.val / p^(e-1) := by
    unfold hdigit
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hdiv]
  have hsum : (proj e x).val + p^(e-1) * (hdigit e x).val = x.val := by
    rw [h1, h2, add_comm]
    exact Nat.div_add_mod x.val (p^(e-1))
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [← Nat.cast_mul, ← Nat.cast_add, ZMod.natCast_eq_natCast_iff]
  show x.val % p^e = ((proj e x).val + p^(e-1) * (hdigit e x).val) % p^e
  rw [hsum]

/-- The expansion is unique: base class + digit determine `x`. -/
theorem hdigit_unique (he : 2 ≤ e) {x y : ZMod (p^e)} (h1 : proj e x = proj e y)
    (h2 : hdigit e x = hdigit e y) : x = y := by
  rw [hdigit_recon he x, hdigit_recon he y, h1, h2]

/-- Units descend along the projection: `IsUnit x ↔ IsUnit (proj e x)`. -/
theorem isUnit_proj (hp : p.Prime) (he : 2 ≤ e) (x : ZMod (p^e)) :
    IsUnit x ↔ IsUnit (proj e x) := by
  haveI : NeZero (p^e) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  haveI : NeZero (p^(e-1)) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  have key : x.val.Coprime (p^e) ↔ (x.val % p^(e-1)).Coprime (p^(e-1)) := by
    have h1 := ZMod.coprime_mod_iff_coprime (x.val) (p^(e-1))
    have h2 : x.val.Coprime (p^e) ↔ x.val.Coprime p :=
      Nat.coprime_pow_right_iff (by omega) _ _
    have h3 : x.val.Coprime (p^(e-1)) ↔ x.val.Coprime p :=
      Nat.coprime_pow_right_iff (by omega) _ _
    rw [h2, h1, h3]
  have e1 : x = (((x.val : ℕ)) : ZMod (p^e)) := (ZMod.natCast_zmod_val x).symm
  have e2 : proj e x = ((((proj e x).val : ℕ)) : ZMod (p^(e-1))) :=
    (ZMod.natCast_zmod_val _).symm
  calc IsUnit x ↔ IsUnit ((((x.val : ℕ))) : ZMod (p^e)) := by rw [← e1]
    _ ↔ x.val.Coprime (p^e) := ZMod.isUnit_iff_coprime _ _
    _ ↔ (x.val % p^(e-1)).Coprime (p^(e-1)) := key
    _ ↔ IsUnit ((((proj e x).val : ℕ)) : ZMod (p^(e-1))) := by
        rw [proj_val]
        exact (ZMod.isUnit_iff_coprime _ _).symm
    _ ↔ IsUnit (proj e x) := by rw [← e2]

/-- The projection sends inverses to inverses. -/
theorem proj_inv {x : ZMod (p^e)} (hp : p.Prime) (he : 2 ≤ e) (hUx : IsUnit x) :
    proj e x⁻¹ = (proj e x)⁻¹ := by
  haveI : NeZero (p^e) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  haveI : NeZero (p^(e-1)) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  have h : proj e x * proj e x⁻¹ = 1 := by
    have h2 := congrArg (proj e) (unit_mul_inv hUx)
    rw [map_mul, map_one] at h2
    exact h2
  exact unit_inv_eq_of_mul_eq_one ((isUnit_proj hp he x).mp hUx) h

/-- The quotient `k_r` satisfies `r.val·(r⁻¹).val = 1 + p^{e-1}·k_r`. -/
theorem Kquot_spec {r : ZMod (p^(e-1))} (hp : p.Prime) (he : 2 ≤ e) (hr : IsUnit r) :
    r.val * (r⁻¹).val = 1 + p^(e-1) * Kquot e r := by
  haveI : NeZero (p^(e-1)) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  have h12 : 1 < p^(e-1) := by
    have hp1 := hp.one_lt
    have hle : p^1 ≤ p^(e-1) := pow_le_pow_right₀ (by omega) (by omega)
    rw [pow_one] at hle
    omega
  haveI : Fact (1 < p^(e-1)) := ⟨h12⟩
  have h2 : (r.val * (r⁻¹).val) % p^(e-1) = 1 := by
    have h1 : r * r⁻¹ = 1 := unit_mul_inv hr
    have h3 := congrArg ZMod.val h1
    rw [ZMod.val_mul, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h12] at h3
    exact h3
  have hr0 : r.val ≠ 0 := by
    intro h0
    have hr00 : r = 0 := by
      rw [← ZMod.natCast_zmod_val r, h0]
      simp
    exact IsUnit.ne_zero hr hr00
  have hri0 : (r⁻¹).val ≠ 0 := by
    intro h0
    have hr00 : r⁻¹ = 0 := by
      rw [← ZMod.natCast_zmod_val (r⁻¹), h0]
      simp
    exact IsUnit.ne_zero (unit_inv_isUnit hr) hr00
  have hpos : 1 ≤ r.val * (r⁻¹).val := Nat.pos_of_ne_zero (mul_ne_zero hr0 hri0)
  have hdvd : p^(e-1) ∣ r.val * (r⁻¹).val - 1 := by
    have hda := Nat.div_add_mod (r.val * (r⁻¹).val) (p^(e-1))
    rw [h2] at hda
    exact ⟨r.val * (r⁻¹).val / p^(e-1), by omega⟩
  have hK : r.val * (r⁻¹).val - 1 = p^(e-1) * Kquot e r := by
    have h0 : (r.val * (r⁻¹).val - 1) % p^(e-1) = 0 := by
      obtain ⟨c, hc⟩ := hdvd
      rw [hc]
      exact Nat.mul_mod_right _ _
    have hda := Nat.div_add_mod (r.val * (r⁻¹).val - 1) (p^(e-1))
    rw [h0, add_zero] at hda
    unfold Kquot
    exact hda.symm
  omega

/-- The quotient is symmetric: `k_{r⁻¹} = k_r`. -/
theorem Kquot_inv (r : ZMod (p^(e-1))) (hp : p.Prime) (hr : IsUnit r) :
    Kquot e r⁻¹ = Kquot e r := by
  haveI : NeZero (p^(e-1)) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  have hri : (r⁻¹)⁻¹ = r := unit_inv_inv hr
  unfold Kquot
  rw [hri, mul_comm]

/-- Membership in a digit set unfolds to the defining property. -/
theorem mem_digitSet {P : Finset (ZMod (p^e))} {r : ZMod (p^(e-1))} {w : ZMod p} :
    w ∈ digitSet e P r ↔ ∃ x ∈ P, proj e x = r ∧ hdigit e x = w := by
  unfold digitSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Finset.mem_filter] at hx
    exact ⟨x, hx.1, hx.2, rfl⟩
  · rintro ⟨x, hxP, hxr, rfl⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨hxP, hxr⟩, rfl⟩

/-- The forced digit, packaged: the top digit of `x⁻¹` is `A_map` of the top
digit of `x`, with `s = (proj e x)⁻¹` and `k = k_{proj e x}`. -/
theorem forced_digit_of_mem (hp : p.Prime) (he : 2 ≤ e) (x : ZMod (p^e)) (hUx : IsUnit x) :
    hdigit e x⁻¹ = A_map ((((proj e x)⁻¹).val : ZMod p)) (((Kquot e (proj e x) : ℕ)) : ZMod p)
      (hdigit e x) := by
  haveI : NeZero (p^e) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  haveI : NeZero (p^(e-1)) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  have hrU : IsUnit (proj e x) := (isUnit_proj hp he x).mp hUx
  have hsinv : proj e x⁻¹ = (proj e x)⁻¹ := proj_inv hp he hUx
  have hKspec := Kquot_spec (r := proj e x) hp he hrU
  have hrs : ((proj e x).val : ℤ) * ((proj e x⁻¹).val : ℤ)
      = 1 + (p:ℤ)^(e-1) * (((Kquot e (proj e x) : ℕ)) : ℤ) := by
    rw [hsinv]
    have h := congrArg (Nat.cast : ℕ → ℤ) hKspec
    push_cast at h
    linarith
  have hexpX : (x.val : ℤ)
      = ((proj e x).val : ℤ) + (p:ℤ)^(e-1) * (((x.val / p^(e-1) : ℕ)) : ℤ) := by
    have hda := Nat.div_add_mod x.val (p^(e-1))
    have h2 : (((p^(e-1) * (x.val / p^(e-1)) + x.val % p^(e-1) : ℕ)) : ℤ)
        = (((x.val : ℕ)) : ℤ) := congrArg _ hda
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at h2
    rw [← proj_val] at h2
    linarith
  have hexpY : (x⁻¹.val : ℤ)
      = ((proj e x⁻¹).val : ℤ) + (p:ℤ)^(e-1) * (((x⁻¹.val / p^(e-1) : ℕ)) : ℤ) := by
    have hda := Nat.div_add_mod x⁻¹.val (p^(e-1))
    have h2 : (((p^(e-1) * (x⁻¹.val / p^(e-1)) + x⁻¹.val % p^(e-1) : ℕ)) : ℤ)
        = (((x⁻¹.val : ℕ)) : ℤ) := congrArg _ hda
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at h2
    rw [← proj_val] at h2
    linarith
  have hinv0 : (x.val : ℤ) * (x⁻¹.val : ℤ) ≡ 1 [ZMOD (p:ℤ)^e] := by
    have h1 : x * x⁻¹ = 1 := unit_mul_inv hUx
    have h2 : (((x.val * x⁻¹.val : ℕ)) : ZMod (p^e)) = (((1 : ℕ)) : ZMod (p^e)) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, h1, Nat.cast_one]
    have h7 : ((((x.val * x⁻¹.val : ℕ) : ℤ)) : ZMod (p^e))
        = ((((1:ℕ) : ℤ)) : ZMod (p^e)) := by
      exact_mod_cast h2
    have hdvd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h7
    rw [Int.modEq_iff_dvd]
    have hpe : (p:ℤ)^e = (((p^e : ℕ)) : ℤ) := by push_cast; ring
    have hmul : (x.val : ℤ) * (x⁻¹.val : ℤ) = (((x.val * x⁻¹.val : ℕ)) : ℤ) := by
      push_cast; ring
    rw [hpe, hmul]
    simpa using hdvd
  have hinv : ((((proj e x).val : ℤ) + (p:ℤ)^(e-1) * (((x.val / p^(e-1) : ℕ)) : ℤ))
      * (((proj e x⁻¹).val : ℤ) + (p:ℤ)^(e-1) * (((x⁻¹.val / p^(e-1) : ℕ)) : ℤ)))
      ≡ 1 [ZMOD (p:ℤ)^e] := by
    rw [← hexpX, ← hexpY]
    exact hinv0
  have hfd := forced_digit hp he hrs hinv
  have hfdZ := (ZMod.intCast_eq_intCast_iff _ _ _).mpr hfd
  simp only [Int.cast_natCast, Int.cast_neg, Int.cast_sub, Int.cast_mul,
    Int.cast_pow] at hfdZ
  rw [hsinv] at hfdZ
  exact hfdZ

/-- The full Fiber-Compatibility Theorem (R185 §1): for a finite set `P` of
units mod `p^e`, `P` is inverse-closed iff every unit base class `r`
satisfies `S_{r⁻¹} = Finset.image A_r S_r`. -/
theorem fiber_compat_iff (hp : p.Prime) (he : 2 ≤ e)
    (P : Finset (ZMod (p^e))) (hU : ∀ x ∈ P, IsUnit x) :
    (∀ x ∈ P, x⁻¹ ∈ P) ↔
      ∀ r : ZMod (p^(e-1)), IsUnit r →
        digitSet e P r⁻¹ =
          (digitSet e P r).image (A_map ((r⁻¹.val : ZMod p)) ((Kquot e r : ZMod p))) := by
  constructor
  · intro hclose r hr
    haveI : NeZero (p^(e-1)) := ⟨pow_ne_zero _ hp.pos.ne'⟩
    haveI : NeZero (p^e) := ⟨pow_ne_zero _ hp.pos.ne'⟩
    have hpdvd : p ∣ p^(e-1) := dvd_pow_self p (by omega)
    have hχ : ∀ z : ZMod (p^(e-1)),
        ZMod.castHom hpdvd (ZMod p) z = (((z.val : ℕ)) : ZMod p) := by
      intro z
      simp only [ZMod.castHom_apply]
      rw [← ZMod.natCast_val]
    have hts : ((((r.val : ℕ))) : ZMod p) * ((((r⁻¹.val : ℕ))) : ZMod p) = 1 := by
      have h1 : r * r⁻¹ = 1 := unit_mul_inv hr
      have h2 := congrArg (ZMod.castHom hpdvd (ZMod p)) h1
      rw [map_mul, map_one, hχ, hχ] at h2
      exact h2
    have hs : ((((r⁻¹.val : ℕ))) : ZMod p) ≠ 0 := by
      intro h0
      have hU' : IsUnit ((((r⁻¹.val : ℕ))) : ZMod p) := by
        have hχr : ZMod.castHom hpdvd (ZMod p) (r⁻¹) = ((((r⁻¹.val : ℕ))) : ZMod p) :=
          hχ _
        rw [← hχr]
        exact IsUnit.map (ZMod.castHom hpdvd (ZMod p)) (unit_inv_isUnit hr)
      have hcop : (r⁻¹).val.Coprime p := (ZMod.isUnit_iff_coprime _ _).mp hU'
      have hndvd : ¬ p ∣ (r⁻¹).val := hp.coprime_iff_not_dvd.mp hcop.symm
      apply hndvd
      have h2 := congrArg ZMod.val h0
      rw [ZMod.val_natCast, ZMod.val_zero] at h2
      refine ⟨(r⁻¹).val / p, ?_⟩
      have hda := Nat.div_add_mod (r⁻¹).val p
      omega
    have hK : Kquot e r⁻¹ = Kquot e r := Kquot_inv r hp hr
    have pc1 : PairClosed ((r⁻¹.val : ZMod p)) ((Kquot e r : ZMod p))
        (digitSet e P r) (digitSet e P r⁻¹) := by
      show ∀ u ∈ digitSet e P r,
        A_map ((r⁻¹.val : ZMod p)) ((Kquot e r : ZMod p)) u ∈ digitSet e P r⁻¹
      intro u hu
      rw [mem_digitSet] at hu
      obtain ⟨x, hxP, hxr, rfl⟩ := hu
      have hUx : IsUnit x := hU x hxP
      have hmem : hdigit e x⁻¹ ∈ digitSet e P r⁻¹ := by
        rw [mem_digitSet]
        exact ⟨x⁻¹, hclose x hxP, by rw [proj_inv hp he hUx, hxr], rfl⟩
      have hfd := forced_digit_of_mem hp he x hUx
      rw [hxr] at hfd
      rw [← hfd]
      exact hmem
    have pc2 : PairClosed ((r.val : ZMod p)) ((Kquot e r : ZMod p))
        (digitSet e P r⁻¹) (digitSet e P r) := by
      show ∀ v ∈ digitSet e P r⁻¹,
        A_map ((r.val : ZMod p)) ((Kquot e r : ZMod p)) v ∈ digitSet e P r
      intro v hv
      rw [mem_digitSet] at hv
      obtain ⟨y, hyP, hyr, rfl⟩ := hv
      have hUy : IsUnit y := hU y hyP
      have hmem : hdigit e y⁻¹ ∈ digitSet e P r := by
        rw [mem_digitSet]
        refine ⟨y⁻¹, hclose y hyP, ?_, rfl⟩
        rw [proj_inv hp he hUy, hyr]
        exact unit_inv_inv hr
      have hfd := forced_digit_of_mem hp he y hUy
      have hrr : ((((proj e y)⁻¹).val : ZMod p)) = ((r.val : ZMod p)) := by
        rw [hyr]
        have h2 : ((r⁻¹)⁻¹ : ZMod (p^(e-1))) = r := unit_inv_inv hr
        rw [h2]
      have hkk : ((((Kquot e (proj e y) : ℕ))) : ZMod p) = ((Kquot e r : ZMod p)) := by
        rw [hyr, hK]
      rw [hrr, hkk] at hfd
      rw [← hfd]
      exact hmem
    exact (fiber_compat_pair_iff hts hs (digitSet e P r) (digitSet e P r⁻¹)).mp ⟨pc1, pc2⟩
  · intro hcompat x hx
    haveI : NeZero (p^(e-1)) := ⟨pow_ne_zero _ hp.pos.ne'⟩
    haveI : NeZero (p^e) := ⟨pow_ne_zero _ hp.pos.ne'⟩
    have hUx : IsUnit x := hU x hx
    have hrU : IsUnit (proj e x) := (isUnit_proj hp he x).mp hUx
    have h := hcompat (proj e x) hrU
    have hfd := forced_digit_of_mem hp he x hUx
    have hmem : hdigit e x⁻¹ ∈ digitSet e P (proj e x)⁻¹ := by
      rw [h, hfd]
      apply Finset.mem_image_of_mem
      rw [mem_digitSet]
      exact ⟨x, hx, rfl, rfl⟩
    rw [mem_digitSet] at hmem
    obtain ⟨y, hyP, hyr, hdigy⟩ := hmem
    have hyeq : y = x⁻¹ := by
      apply hdigit_unique he
      · rw [hyr, proj_inv hp he hUx]
      · exact hdigy
    rw [← hyeq]
    exact hyP

end FiberCompatLift
