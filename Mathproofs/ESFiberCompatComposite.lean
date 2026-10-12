/-
  ESFiberCompatComposite.lean — R192 Composite Fiber-Compatibility Theorem: the R185 machinery over composite moduli (D|n), with the §2 D|n lemma.

  Paper: papers/fiber-compatibility-composite-suppression-October-11-2026/
  Status: [PROVED] — fiber_compat_iffC, forced_digit_of_memC (+ composite digit/projection API)
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); machine-checked on bakkie (R210), `lake build` exit 0, zero sorrys, axioms standard-only.
-/

import Mathlib
import Mathproofs.ESFiberCompat

/-!
# R192 Composite Fiber-Compatibility Theorem (Round 198, Lean formalization lane)

R192 (dossier `~/workspace/math-unsolved/ROUND192_DOSSIER.md`) lifted R185's
Fiber-Compatibility Theorem from prime powers to general composite modulus
via CRT decomposition, and refuted the naive component-wise reduction
(Correlation Break Theorem [COMPUTED]).

Setup: `m = ∏ p_i^{e_i}` with mixed base `n = ∏ p_i^{e_i-1}` (squarefree
primes folded in) and digit modulus `D = ∏ p_i`, so `m = n * D` and
`D ∣ n`. Every `x mod m` writes uniquely as `x = r + n·u` with `r ∈ ℤ/n`,
`u ∈ ℤ/D`. For finite `P ⊂ ℤ`, `π_m(P)` its projection,
`S_r = { u ∈ ℤ/D : r + n·u ∈ π_m(P) }`. For unit `r mod n`: `r* = r⁻¹ mod n`,
`k = (rr*−1)/n ∈ ℤ`, `A_r(u) = (−u(r*)² − kr*) mod D` (forced Hensel digit map).

**Theorem (R192 §2).** `π_m(P)` is inverse-closed ⟺ for every unit `r mod n`,
`S_{r*} = A_r(S_r)`.

The proof is R185's proof verbatim once `D ∣ n` kills the `n²uu*` term.
That is the new mathematics here, and it is what this module formalizes:

1. `A_mapC`: the composite digit map on `ZMod D` (no primality needed —
   only that the slope `−s²` is a unit), with injectivity, the involution
   `A_{r*} ∘ A_r = id`, and the pair-level iff (card argument, as in R194).
2. `forced_digit_dvd` (the new lemma): with `rs = 1 + nk` and
   `(r + nu)(s + nv) = 1 + mt`, where `n·D ∣ m` and `D ∣ n`, the digit is
   forced: `D ∣ v + u·s² + k·s`. The `n²·u·v` term vanishes mod `D`.
3. `fiber_compat_iffC`: the full `π(P)` lift-set packaging for composite
   `m = n·D` — `P` inverse-closed ⟺ digit-compatibility at every unit base
   class. Promotes R192's Composite Fiber-Compatibility Theorem
   [PROVED*] → [PROVED].
4. `proj_inv_closed` / `proj_inv_closed_zmod`: the (⇒) projection theorem
   (R192 §3) — a ring hom sends inverse-closed sets to inverse-closed
   sets (projection `ℤ/m → ℤ/n` is a ring hom, CRT inversion is
   componentwise). Stated without a global inverse, so it applies to any
   commutative ring.

Cited, not re-formalized: the empirical iff on 44 composite moduli
[COMPUTED ×2], the Correlation Break Theorem and its minimal witnesses
[COMPUTED], the 441 correlation-hole anatomy [COMPUTED] — R192 §§3–4.

Imports `Mathproofs.ESFiberCompat` for the ZMod unit-inverse API
(`FiberCompatLift.unit_mul_inv`, `unit_inv_eq_of_mul_eq_one`,
`unit_inv_isUnit`, `unit_inv_inv`) — referenced only, not modified
(R190/R194 [PROVED]).

Preprint protocol note: when the composite theory preprint is written, it
must reference this module and `fiber_compat_iffC` by name.
-/

namespace ESFiberCompatComposite

open FiberCompatLift

variable {n D m : ℕ} [NeZero n] [NeZero D] [NeZero m]

/-!
## §1. The composite digit map (no primality needed)
-/

/-- The composite forced Hensel digit map: `A_r(u) = −u·(r*)² − k·r*` on
`ZMod D`. Here `s` plays the role of `r*`, `k` the shared quotient. -/
def A_mapC (s k : ZMod D) : ZMod D → ZMod D := fun u => -(u * s^2) - k * s

/-- The composite digit map is injective: an affine map whose slope `−s²`
is a unit (this is all that prime-power primality bought in R194). -/
theorem A_mapC_injective {s k : ZMod D} (hs : IsUnit s) :
    Function.Injective (A_mapC s k) := by
  intro a b h
  simp only [A_mapC] at h
  have h2 : a * (-(s^2)) = b * (-(s^2)) := by linear_combination h
  exact (hs.pow 2).neg.mul_right_cancel h2

/-- The composite digit map is an explicit equivalence (two-sided inverse). -/
def A_equivC (s k : ZMod D) (hs : IsUnit s) : ZMod D ≃ ZMod D where
  toFun := A_mapC s k
  invFun := fun v => (v + k * s) * (-(s^2))⁻¹
  left_inv := fun u => by
    obtain ⟨uinv, hu⟩ := (hs.pow 2).neg
    have hm : (-(s^2) : ZMod D) * (-(s^2))⁻¹ = 1 := unit_mul_inv (hs.pow 2).neg
    show ((-(u * s^2) - k * s) + k * s) * (-(s^2))⁻¹ = u
    have e1 : (-(u * s^2) - k * s) + k * s = -(u * s^2) := by ring
    have e2 : (-(u * s^2) : ZMod D) = u * (-(s^2)) := by ring
    rw [e1, e2, mul_assoc, hm, mul_one]
  right_inv := fun v => by
    obtain ⟨uinv, hu⟩ := (hs.pow 2).neg
    have hm : (-(s^2) : ZMod D)⁻¹ * s^2 = -1 := by
      have h1 : (-(s^2) : ZMod D)⁻¹ * (-(s^2)) = 1 := by
        rw [mul_comm]; exact unit_mul_inv (hs.pow 2).neg
      have h2 : (-(s^2) : ZMod D)⁻¹ * s^2
          = -((-(s^2) : ZMod D)⁻¹ * (-(s^2))) := by ring
      rw [h2, h1]
    show -(((v + k * s) * (-(s^2))⁻¹) * s^2) - k * s = v
    have e1 : ((v + k * s) * (-(s^2))⁻¹) * s^2 = -((v + k * s)) := by
      rw [mul_assoc, hm, mul_neg, mul_one]
    rw [e1]
    ring

/-- `A_{r*} ∘ A_r = id` over `ZMod D`: applying the digit map twice (shared
`k`, inverse slopes `t·s = 1`) returns the digit. Same
`linear_combination` certificate as R194 — no primality used. -/
theorem A_mapC_invol {s t k : ZMod D} (hts : t * s = 1) (u : ZMod D) :
    A_mapC s k (A_mapC t k u) = u := by
  have hts2 : t^2 * s^2 = 1 := by rw [← mul_pow, hts, one_pow]
  simp only [A_mapC]
  linear_combination u * hts2 + k * s * hts

/-- Symmetric form: `A_r ∘ A_{r*} = id`. -/
theorem A_mapC_invol_symm {s t k : ZMod D} (hts : t * s = 1) (u : ZMod D) :
    A_mapC t k (A_mapC s k u) = u :=
  A_mapC_invol (by rw [mul_comm]; exact hts) u

/-!
## §2. The `D ∣ n` lemma — the new mathematics

R185's forced-digit computation leaves an `n²uu*` term; for prime powers
`n = p^{e-1}` absorbs it into the `p^e` modulus. For composite `m = n·D`
the key step is: `D ∣ n` kills the `n²uu*` term mod `D`, so the inverse's
digit is forced by the same affine map. This is the only new ingredient
in R192's proof.
-/

/-- The composite forced-digit lemma (R192 §2): with `rs = 1 + nk` and
`(r + n·u)(s + n·v) = 1 + m·t` where `n·D ∣ m` and `D ∣ n`, the digit is
forced: `D ∣ v + u·s² + k·s`. -/
theorem forced_digit_dvd {r s k u v nD dD mD t : ℤ} (hn0 : nD ≠ 0)
    (hm : nD * dD ∣ mD) (hDn : dD ∣ nD) (hrs : r * s = 1 + nD * k)
    (hinv : (r + nD * u) * (s + nD * v) = 1 + mD * t) :
    dD ∣ (v + u * s ^ 2 + k * s) := by
  obtain ⟨c, hc⟩ := hm
  obtain ⟨d, hd⟩ := hDn
  have e1 : (r + nD * u) * (s + nD * v)
      = 1 + nD * k + nD * (u * s + r * v) + nD ^ 2 * (u * v) := by
    rw [show (r + nD * u) * (s + nD * v)
      = r * s + nD * (u * s + r * v) + nD ^ 2 * (u * v) by ring, hrs]
  have hcancel : k + (u * s + r * v) + nD * (u * v) = dD * (c * t) := by
    have h := hinv
    rw [e1, hc] at h
    have h2 : nD * (k + (u * s + r * v) + nD * (u * v)) = nD * (dD * (c * t)) := by
      linear_combination h
    exact mul_left_cancel₀ hn0 h2
  have hrv : r * v * s = v + v * (nD * k) := by
    have e : r * v * s = v * (r * s) := by ring
    rw [e, hrs]; ring
  refine ⟨c * t * s - d * (v * k + u * v * s), ?_⟩
  linear_combination s * hcancel - hrv - (v * k + u * v * s) * hd

/-!
## §3. The pair-level composite iff
-/

/-- Inverse-closure at one inverse pair, in composite digit form. -/
def PairClosedC (s k : ZMod D) (S S' : Finset (ZMod D)) : Prop :=
  ∀ u ∈ S, A_mapC s k u ∈ S'

/-- The pair-level composite Fiber-Compatibility iff (R192 Theorem, kernel
form): inverse-closure at one inverse pair (digit form, both directions —
the dossier's `(⇒)` applies closure to `r*` and uses the involution for the
card argument) holds exactly when `S_{r*} = Finset.image A_r S_r`. -/
theorem fiber_compat_pair_iffC {s t k : ZMod D} (hts : t * s = 1) (hs : IsUnit s)
    (S S' : Finset (ZMod D)) :
    (PairClosedC s k S S' ∧ PairClosedC t k S' S)
      ↔ S' = Finset.image (A_mapC s k) S := by
  constructor
  · rintro ⟨hS, hS'⟩
    simp only [PairClosedC] at hS hS'
    have hinj : Function.Injective (A_mapC s k) := A_mapC_injective hs
    have htU : IsUnit t := by
      obtain ⟨u, hu⟩ := hs
      refine ⟨⟨t, s, hts, ?_⟩, rfl⟩
      rw [mul_comm]
      exact hts
    have hinj' : Function.Injective (A_mapC t k) := A_mapC_injective htU
    have himg : Finset.image (A_mapC s k) S ⊆ S' := by
      intro v hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      exact hS u hu
    have himg' : Finset.image (A_mapC t k) S' ⊆ S := by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact hS' w hw
    have hcc : S.card = S'.card := by
      have h1 : (Finset.image (A_mapC s k) S).card ≤ S'.card := Finset.card_le_card himg
      have h2 : (Finset.image (A_mapC t k) S').card ≤ S.card := Finset.card_le_card himg'
      rw [Finset.card_image_of_injective _ hinj] at h1
      rw [Finset.card_image_of_injective _ hinj'] at h2
      omega
    have hfin : S'.card ≤ (Finset.image (A_mapC s k) S).card := by
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
      rw [A_mapC_invol_symm hts]
      exact hu

/-!
## §4. The (⇒) projection theorem (R192 §3)

The naive reduction's surviving direction: `ℤ/m → ℤ/n` is a ring
homomorphism, CRT inversion is componentwise, so the projection of an
inverse-closed set is inverse-closed. Inverse-closure is stated without a
global inverse, so this holds for any commutative ring.
-/

/-- The projection theorem (R192 §3, naive-reduction (⇒)): a ring hom
sends inverse-closed sets to inverse-closed sets. -/
theorem proj_inv_closed {R S : Type*} [CommRing R] [CommRing S] [DecidableEq R]
    [DecidableEq S] (φ : R →+* S)
    (P : Finset R) (hU : ∀ a ∈ P, IsUnit a)
    (hclose : ∀ a ∈ P, ∀ b : R, a * b = 1 → b ∈ P) :
    ∀ s ∈ Finset.image (⇑φ) P, ∀ c : S, s * c = 1 → c ∈ Finset.image (⇑φ) P := by
  intro s hs c hsc
  obtain ⟨a, haP, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨u, hu⟩ := hU a haP
  have hmem : ((u⁻¹ : Rˣ) : R) ∈ P :=
    hclose a haP _ (by rw [← hu]; exact Units.mul_inv u)
  have h2 : φ a * φ ((u⁻¹ : Rˣ) : R) = 1 := by
    have h3 : a * ((u⁻¹ : Rˣ) : R) = 1 := by rw [← hu]; exact Units.mul_inv u
    rw [← map_mul, h3, map_one]
  have hc : c = φ ((u⁻¹ : Rˣ) : R) := by
    calc c = 1 * c := (one_mul c).symm
      _ = (φ ((u⁻¹ : Rˣ) : R) * φ a) * c := by rw [mul_comm _ (φ a), h2]
      _ = φ ((u⁻¹ : Rˣ) : R) * (φ a * c) := by rw [mul_assoc]
      _ = φ ((u⁻¹ : Rˣ) : R) * 1 := by rw [hsc]
      _ = φ ((u⁻¹ : Rˣ) : R) := mul_one _
  rw [hc]
  exact Finset.mem_image_of_mem _ hmem

/-- The projection theorem for `ZMod`: the projection `ℤ/m → ℤ/n`
(`n ∣ m`) sends inverse-closed unit sets to inverse-closed unit sets. -/
theorem proj_inv_closed_zmod (hnm : n ∣ m) (P : Finset (ZMod m))
    (hU : ∀ a ∈ P, IsUnit a)
    (hclose : ∀ a ∈ P, ∀ b : ZMod m, a * b = 1 → b ∈ P) :
    ∀ s ∈ Finset.image (⇑(ZMod.castHom hnm (ZMod n))) P, ∀ c : ZMod n,
      s * c = 1 → c ∈ Finset.image (⇑(ZMod.castHom hnm (ZMod n))) P :=
  proj_inv_closed (ZMod.castHom hnm (ZMod n)) P hU hclose

/-!
## §5. The full composite `π(P)` lift-set packaging

For `m = n * D` with `D ∣ n`: from a finite set `P : Finset (ZMod m)` of
units, build the composite digit sets `S_r = { u : r + n·u ∈ P }` and prove
the full iff — `P` inverse-closed ⟺ every unit base class `r` satisfies
`S_{r⁻¹} = Finset.image A_r S_r`. This promotes R192's Composite
Fiber-Compatibility Theorem [PROVED*] → [PROVED].
-/

/-- The natural projection `ZMod m →+* ZMod n` (reduction mod `n`). -/
def projC (hnm : n ∣ m) : ZMod m →+* ZMod n := ZMod.castHom hnm (ZMod n)

/-- The composite Hensel digit of `x : ZMod m`: the `u` with `x = r + n·u`. -/
def hdigitC (x : ZMod m) : ZMod D :=
  ((x.val / n : ℕ) : ZMod D)

/-- The composite digit set `S_r = { u : r + n·u ∈ P }` of a base class `r`. -/
def digitSetC (hnm : n ∣ m) (P : Finset (ZMod m)) (r : ZMod n) : Finset (ZMod D) :=
  (P.filter (fun x => projC hnm x = r)).image (hdigitC (n := n) (D := D) (m := m))

/-- The shared quotient `k_r = (r.val·(r⁻¹).val − 1)/n`; symmetric in
`r, r⁻¹`, matching the kernel's shared `k`. -/
def KquotC (r : ZMod n) : ℕ :=
  (r.val * (r⁻¹).val - 1) / n

/-- The projection reads off the low digits: `(projC x).val = x.val % n`. -/
theorem projC_val (hnm : n ∣ m) (x : ZMod m) : (projC hnm x).val = x.val % n := by
  unfold projC
  rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.val_natCast]

/-- Digit expansion: `x` is rebuilt from its base class and its digit. -/
theorem hdigitC_recon (hnm : n ∣ m) (hn : 1 < n) (hmd : m = n * D) (x : ZMod m) :
    x = (((projC hnm x).val : ℕ) : ZMod m)
      + (((n : ℕ)) : ZMod m) * ((((hdigitC (n := n) (D := D) x).val : ℕ)) : ZMod m) := by
  have h1 : (projC hnm x).val = x.val % n := projC_val hnm x
  have hdiv : x.val / n < D := by
    have hlt : x.val < n * D := by
      have h1x := ZMod.val_lt x
      omega
    by_contra hcon
    have hle : D ≤ x.val / n := not_lt.mp hcon
    have hda := Nat.div_add_mod x.val n
    have key : n * D ≤ x.val := by
      have hle2 : n * D ≤ n * (x.val / n) := Nat.mul_le_mul le_rfl hle
      omega
    omega
  have h2 : (hdigitC (n := n) (D := D) x).val = x.val / n := by
    unfold hdigitC
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hdiv]
  have hsum : (projC hnm x).val + n * (hdigitC (n := n) (D := D) x).val = x.val := by
    rw [h1, h2, add_comm]
    exact Nat.div_add_mod x.val n
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [← Nat.cast_mul, ← Nat.cast_add, ZMod.natCast_eq_natCast_iff]
  show x.val % m = ((projC hnm x).val + n * (hdigitC (n := n) (D := D) x).val) % m
  rw [hsum]

/-- The expansion is unique: base class + digit determine `x`. -/
theorem hdigitC_unique (hnm : n ∣ m) (hn : 1 < n) (hmd : m = n * D) {x y : ZMod m}
    (h1 : projC hnm x = projC hnm y)
    (h2 : hdigitC (n := n) (D := D) x = hdigitC (n := n) (D := D) y) : x = y := by
  rw [hdigitC_recon hnm hn hmd x, hdigitC_recon hnm hn hmd y, h1, h2]

/-- The projection sends unit inverses to inverses (ZMod's Bézout inverse). -/
theorem projC_inv (hnm : n ∣ m) {x : ZMod m} (hUx : IsUnit x) :
    projC hnm x⁻¹ = (projC hnm x)⁻¹ := by
  have h : projC hnm x * projC hnm x⁻¹ = 1 := by
    have h2 := congrArg (projC hnm) (unit_mul_inv hUx)
    rw [map_mul, map_one] at h2
    exact h2
  exact unit_inv_eq_of_mul_eq_one (IsUnit.map _ hUx) h

/-- The quotient `k_r` satisfies `r.val·(r⁻¹).val = 1 + n·k_r`. -/
theorem KquotC_spec (hn : 1 < n) {r : ZMod n} (hr : IsUnit r) :
    r.val * (r⁻¹).val = 1 + n * KquotC r := by
  haveI : Fact (1 < n) := ⟨hn⟩
  have hdvd : n ∣ r.val * (r⁻¹).val - 1 := by
    have hda := Nat.div_add_mod (r.val * (r⁻¹).val) n
    have h2 : (r.val * (r⁻¹).val) % n = 1 := by
      have h1 : r * r⁻¹ = 1 := unit_mul_inv hr
      have h3 := congrArg ZMod.val h1
      rw [ZMod.val_mul, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hn] at h3
      exact h3
    rw [h2] at hda
    exact ⟨r.val * (r⁻¹).val / n, by omega⟩
  have hK : r.val * (r⁻¹).val - 1 = n * KquotC r := by
    have h0 : (r.val * (r⁻¹).val - 1) % n = 0 := by
      obtain ⟨c, hc⟩ := hdvd
      rw [hc]
      exact Nat.mul_mod_right _ _
    have hda := Nat.div_add_mod (r.val * (r⁻¹).val - 1) n
    rw [h0, add_zero] at hda
    unfold KquotC
    exact hda.symm
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
  omega

/-- The quotient is symmetric: `k_{r⁻¹} = k_r`. -/
theorem KquotC_inv (r : ZMod n) (hr : IsUnit r) :
    KquotC r⁻¹ = KquotC r := by
  have hri : (r⁻¹)⁻¹ = r := unit_inv_inv hr
  unfold KquotC
  rw [hri, mul_comm]

/-- Membership in a composite digit set unfolds to the defining property. -/
theorem mem_digitSetC (hnm : n ∣ m) {P : Finset (ZMod m)} {r : ZMod n} {w : ZMod D} :
    w ∈ digitSetC (n := n) (D := D) (m := m) hnm P r
      ↔ ∃ x ∈ P, projC hnm x = r ∧ hdigitC (n := n) (D := D) x = w := by
  unfold digitSetC
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Finset.mem_filter] at hx
    exact ⟨x, hx.1, hx.2, rfl⟩
  · rintro ⟨x, hxP, hxr, rfl⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨hxP, hxr⟩, rfl⟩

/-- The forced digit, packaged: the digit of `x⁻¹` is `A_mapC` of the digit
of `x`, with `s = (projC x)⁻¹` and `k = k_{projC x}` — via the `D ∣ n`
lemma (§2), the only new ingredient over R194. -/
theorem forced_digit_of_memC (hnm : n ∣ m) (hn : 1 < n) (hmd : m = n * D)
    (hDn : D ∣ n) (x : ZMod m) (hUx : IsUnit x) :
    hdigitC (n := n) (D := D) x⁻¹ = A_mapC ((((projC hnm x)⁻¹).val : ZMod D))
      (((KquotC (projC hnm x) : ℕ)) : ZMod D)
      (hdigitC (n := n) (D := D) x) := by
  have hnN : (n:ℤ) ≠ 0 := by
    have h : n ≠ 0 := by omega
    exact_mod_cast h
  have hsinv : projC hnm x⁻¹ = (projC hnm x)⁻¹ := projC_inv hnm hUx
  have hKspec := KquotC_spec (r := projC hnm x) hn (IsUnit.map _ hUx)
  set u : ℤ := (((x.val / n : ℕ)) : ℤ) with hu
  set v : ℤ := (((x⁻¹.val / n : ℕ)) : ℤ) with hv
  set sv : ℤ := (((projC hnm x⁻¹).val : ℕ) : ℤ) with hsv
  set kv : ℤ := (((KquotC (projC hnm x) : ℕ)) : ℤ) with hkv
  have hrs : ((projC hnm x).val : ℤ) * sv = 1 + (n:ℤ) * kv := by
    rw [hsv, hsinv]
    have h := congrArg (Nat.cast : ℕ → ℤ) hKspec
    push_cast at h
    rw [hkv]
    linarith
  have hexpX : (x.val : ℤ)
      = ((projC hnm x).val : ℤ) + (n:ℤ) * u := by
    have hda := Nat.div_add_mod x.val n
    have h2 : (((n * (x.val / n) + x.val % n : ℕ)) : ℤ)
        = (((x.val : ℕ)) : ℤ) := congrArg _ hda
    rw [Nat.cast_add, Nat.cast_mul] at h2
    rw [← projC_val hnm] at h2
    rw [hu]
    linarith
  have hexpY : (x⁻¹.val : ℤ)
      = ((projC hnm x⁻¹).val : ℤ) + (n:ℤ) * v := by
    have hda := Nat.div_add_mod x⁻¹.val n
    have h2 : (((n * (x⁻¹.val / n) + x⁻¹.val % n : ℕ)) : ℤ)
        = (((x⁻¹.val : ℕ)) : ℤ) := congrArg _ hda
    rw [Nat.cast_add, Nat.cast_mul] at h2
    rw [← projC_val hnm] at h2
    rw [hv]
    linarith
  have hdvd : (m:ℤ) ∣ (x.val:ℤ) * (x⁻¹.val:ℤ) - 1 := by
    have h1 : x * x⁻¹ = 1 := unit_mul_inv hUx
    have h3 : (((x.val * x⁻¹.val : ℕ)) : ZMod m) = (((1:ℕ)) : ZMod m) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, h1, Nat.cast_one]
    have h2 : (((x.val * x⁻¹.val : ℕ) : ℤ) : ZMod m) = (((1:ℕ) : ℤ) : ZMod m) := by
      exact_mod_cast h3
    have h4 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h2
    obtain ⟨t', ht'⟩ := h4
    refine ⟨-t', by push_cast at ht' ⊢; linarith⟩
  obtain ⟨t, ht⟩ := hdvd
  have hinv : (((projC hnm x).val : ℤ) + (n:ℤ) * u)
      * (((projC hnm x⁻¹).val : ℤ) + (n:ℤ) * v)
      = 1 + (m:ℤ) * t := by
    rw [← hexpX, ← hexpY]
    have h5 : (x.val:ℤ) * (x⁻¹.val:ℤ) = ((((x.val * x⁻¹.val : ℕ)) : ℤ)) := by
      push_cast; ring
    have hmul : ((((x.val * x⁻¹.val : ℕ)) : ℤ)) = 1 + (m:ℤ) * t := by
      have := ht
      omega
    rw [h5, hmul]
  have hfd := forced_digit_dvd (nD := (n:ℤ)) (dD := (D:ℤ)) (mD := (m:ℤ)) (t := t) hnN
    (by rw [hmd]; push_cast; exact dvd_rfl)
    (by exact_mod_cast hDn) hrs hinv
  have key : (v : ZMod D)
      = -(u : ZMod D) * (sv : ZMod D)^2 - (kv : ZMod D) * (sv : ZMod D) := by
    have ecast : (-(u : ZMod D) * (sv : ZMod D)^2 - (kv : ZMod D) * (sv : ZMod D))
        = (((-(u * sv^2) - kv * sv : ℤ)) : ZMod D) := by push_cast; ring
    rw [ecast, ZMod.intCast_eq_intCast_iff_dvd_sub]
    have e4 : (-(u * sv^2) - kv * sv) - v = -(v + u * sv^2 + kv * sv) := by ring
    rw [e4]
    exact dvd_neg.mpr hfd
  rw [hsinv] at hsv
  have eL : hdigitC (n := n) (D := D) x⁻¹ = (v : ZMod D) := by
    unfold hdigitC
    rw [hv, Int.cast_natCast]
  have eR : A_mapC ((((projC hnm x)⁻¹).val : ZMod D))
      (((KquotC (projC hnm x) : ℕ)) : ZMod D)
      (hdigitC (n := n) (D := D) x)
      = -(u : ZMod D) * (sv : ZMod D)^2 - (kv : ZMod D) * (sv : ZMod D) := by
    have eu : (u : ZMod D) = ((x.val / n : ℕ) : ZMod D) := by rw [hu, Int.cast_natCast]
    have esv : (sv : ZMod D) = (((projC hnm x)⁻¹).val : ZMod D) := by
      rw [hsv, Int.cast_natCast]
    have ekv : (kv : ZMod D) = ((KquotC (projC hnm x) : ZMod D)) := by
      rw [hkv, Int.cast_natCast]
    have ehu : hdigitC (n := n) (D := D) x = ((x.val / n : ℕ) : ZMod D) := rfl
    simp only [A_mapC, ehu, eu, esv, ekv]
    ring
  rw [eL, eR]
  exact key

/-- The full Composite Fiber-Compatibility Theorem (R192 §2): for a finite
set `P` of units mod `m = n·D` with `D ∣ n`, `P` is inverse-closed iff
every unit base class `r` satisfies
`S_{r⁻¹} = Finset.image A_r S_r`. -/
theorem fiber_compat_iffC (hnm : n ∣ m) (hn : 1 < n) (hmd : m = n * D)
    (hDn : D ∣ n) (P : Finset (ZMod m)) (hU : ∀ x ∈ P, IsUnit x) :
    (∀ x ∈ P, x⁻¹ ∈ P) ↔
      ∀ r : ZMod n, IsUnit r →
        digitSetC (n := n) (D := D) (m := m) hnm P r⁻¹ =
          (digitSetC (n := n) (D := D) (m := m) hnm P r).image
            (A_mapC ((r⁻¹.val : ZMod D)) ((KquotC r : ZMod D))) := by
  haveI : Fact (1 < n) := ⟨hn⟩
  constructor
  · intro hclose r hr
    have hχ : ∀ z : ZMod n,
        ZMod.castHom hDn (ZMod D) z = (((z.val : ℕ)) : ZMod D) := by
      intro z
      simp only [ZMod.castHom_apply]
      rw [← ZMod.natCast_val]
    have hts : ((((r.val : ℕ))) : ZMod D) * ((((r⁻¹.val : ℕ))) : ZMod D) = 1 := by
      have h1 : r * r⁻¹ = 1 := unit_mul_inv hr
      have h2 := congrArg (ZMod.castHom hDn (ZMod D)) h1
      rw [map_mul, map_one, hχ, hχ] at h2
      exact h2
    have hs : IsUnit ((((r⁻¹.val : ℕ))) : ZMod D) := by
      have hU' : IsUnit (ZMod.castHom hDn (ZMod D) (r⁻¹)) :=
        IsUnit.map (ZMod.castHom hDn (ZMod D)) (unit_inv_isUnit hr)
      rw [hχ] at hU'
      exact hU'
    have hK : KquotC r⁻¹ = KquotC r := KquotC_inv r hr
    have pc1 : PairClosedC ((r⁻¹.val : ZMod D)) ((KquotC r : ZMod D))
        (digitSetC (n := n) (D := D) (m := m) hnm P r)
        (digitSetC (n := n) (D := D) (m := m) hnm P r⁻¹) := by
      show ∀ u ∈ digitSetC (n := n) (D := D) (m := m) hnm P r,
        A_mapC ((r⁻¹.val : ZMod D)) ((KquotC r : ZMod D)) u
          ∈ digitSetC (n := n) (D := D) (m := m) hnm P r⁻¹
      intro u hu
      rw [mem_digitSetC hnm] at hu
      obtain ⟨x, hxP, hxr, rfl⟩ := hu
      have hUx : IsUnit x := hU x hxP
      have hmem : hdigitC (n := n) (D := D) x⁻¹
          ∈ digitSetC (n := n) (D := D) (m := m) hnm P r⁻¹ := by
        rw [mem_digitSetC hnm]
        exact ⟨x⁻¹, hclose x hxP, by rw [projC_inv hnm hUx, hxr], rfl⟩
      have hfd := forced_digit_of_memC hnm hn hmd hDn x hUx
      rw [hxr] at hfd
      rw [← hfd]
      exact hmem
    have pc2 : PairClosedC ((r.val : ZMod D)) ((KquotC r : ZMod D))
        (digitSetC (n := n) (D := D) (m := m) hnm P r⁻¹)
        (digitSetC (n := n) (D := D) (m := m) hnm P r) := by
      show ∀ v ∈ digitSetC (n := n) (D := D) (m := m) hnm P r⁻¹,
        A_mapC ((r.val : ZMod D)) ((KquotC r : ZMod D)) v
          ∈ digitSetC (n := n) (D := D) (m := m) hnm P r
      intro v hv
      rw [mem_digitSetC hnm] at hv
      obtain ⟨y, hyP, hyr, rfl⟩ := hv
      have hUy : IsUnit y := hU y hyP
      have hmem : hdigitC (n := n) (D := D) y⁻¹
          ∈ digitSetC (n := n) (D := D) (m := m) hnm P r := by
        rw [mem_digitSetC hnm]
        refine ⟨y⁻¹, hclose y hyP, ?_, rfl⟩
        rw [projC_inv hnm hUy, hyr]
        exact unit_inv_inv hr
      have hfd := forced_digit_of_memC hnm hn hmd hDn y hUy
      have hrr : ((((projC hnm y)⁻¹).val : ZMod D)) = ((r.val : ZMod D)) := by
        rw [hyr]
        have h2 : ((r⁻¹)⁻¹ : ZMod n) = r := unit_inv_inv hr
        rw [h2]
      have hkk : ((((KquotC (projC hnm y) : ℕ))) : ZMod D)
          = ((KquotC r : ZMod D)) := by
        rw [hyr, hK]
      rw [hrr, hkk] at hfd
      rw [← hfd]
      exact hmem
    exact (fiber_compat_pair_iffC hts hs _ _).mp ⟨pc1, pc2⟩
  · intro hcompat x hx
    have hUx : IsUnit x := hU x hx
    have hrU : IsUnit (projC hnm x) := IsUnit.map _ hUx
    have h := hcompat (projC hnm x) hrU
    have hfd := forced_digit_of_memC hnm hn hmd hDn x hUx
    have hmem : hdigitC (n := n) (D := D) (m := m) x⁻¹
        ∈ digitSetC (n := n) (D := D) (m := m) hnm P (projC hnm x)⁻¹ := by
      rw [h, hfd]
      apply Finset.mem_image_of_mem
      rw [mem_digitSetC hnm]
      exact ⟨x, hx, rfl, rfl⟩
    rw [mem_digitSetC hnm] at hmem
    obtain ⟨y, hyP, hyr, hdigy⟩ := hmem
    have hyeq : y = x⁻¹ := by
      apply hdigitC_unique hnm hn hmd
      · rw [hyr, projC_inv hnm hUx]
      · exact hdigy
    rw [← hyeq]
    exact hyP

end ESFiberCompatComposite
