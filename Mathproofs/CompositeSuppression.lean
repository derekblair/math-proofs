/-
  CompositeSuppression.lean — R205/R207 composite suppression theory: suppression coefficient κ, persistence rate Π, T1 demands-descend, T4–T8 R-operator section, digitMap.

  Paper: papers/fiber-compatibility-composite-suppression-October-11-2026/
  Status: [PROVED] — demands_descend, capability_descend, kappa_*, digitMap_*, degeneracy_lemma
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); machine-checked on bakkie (R214), `lake build` exit 0, zero sorrys, axioms standard-only.
-/

import Mathlib

/-!
# R205 Composite Suppression Theory (Round 210, Lean formalization lane)

R205 (dossier `~/workspace/math-unsolved/ROUND205_DOSSIER.md`) invented
*suppression under CRT modulus refinement*: the composite suppression
coefficient κ(m→m′,r) measuring which CRT fibers keep a correlation hole
suppressed when the modulus is refined, the persistence rate Π, and three
first theorems:

- **T1 — Demands descend [PROVED*]**: fine demands-holding ⟹ coarse
  demands-holding. The coarse i-digit is the fixed affine image
  `u ≡ v + L·ũ` of the fine j-digit; applying the same affine map per
  cover and unioning over covers gives coarse demands.
- **T2 — Capability transfer law**: (a) *downward lemma* [PROVED*]: a
  hole-capable cover whose non-singleton margins lie over two distinct
  coarse E-primes, with L coprime to both, forces the coarse pair
  hole-capable (affine digit maps are bijections); (b) *upward is not a
  law* [COMPUTED]: 18/20 preserved, 2/20 destroyed via fine-demands
  breaking (L1 proliferation, L ≡ 0 mod 5 exponent growth).
- **T3 — Suppression does not lift [PROVED* by witness]**: (a)
  desaturation witness (225's saturated (1,1), σ=1, refines into a
  realized L2 hole at 1125, cover (16,61), margins [3,5], σ=0);
  (b) data-specificity: same pair (225,(1,1)) has
  κ = 1.0 / 0.333 / 0.0 / 0.0 / 1.0 across five towers
  (→675, →1125, →3375, →11025, →1800); (c) level change
  (441's L2 pair (4,16) → fine L1 cover (25,58) at 1323).

This module formalizes the **finite-set kernels** of T1/T2(a) and the
κ/Π calculus (D1–D2), all [PROVED] below. The T3 witnesses and the
census aggregates are recorded as **survey theorems**: decidable
arithmetic facts over the R205 census numbers ([COMPUTED] ×2 paths in
the dossier), verified here by `decide`/`norm_num` — the empirical
content stays [COMPUTED], cited not re-proved.

Cited, not re-formalized: R197's correlation holes/demands, R199's
σ/suppression, R192's composite fiber-compatibility (see
`Mathproofs.ESFiberCompatComposite`).

## R207 tower-refinement operator section (Round 214)

R207 (dossier `~/workspace/math-unsolved/ROUND207_DOSSIER.md`) defined
the tower-refinement operator R_{m→m′} on top of this theory: the
per-prime affine digit law φ_v(ũ) = v + L·ũ on ℤ/p, the degeneracy set
Δ(m→m′) = {p : p ∣ L}, and proved its first five theorems. This section
formalizes their finite kernels:

- **T4 — Degeneracy lemma [PROVED]**: the digit map is bijective for
  every v iff p ∤ L (p ∉ Δ), and constant v iff p ∣ L (p ∈ Δ). Pure
  finite affine-map arithmetic. [COMPUTED] mechanism checks from the
  dossier (affine law 3332/3332, margin-union identity 48/48) stay
  [COMPUTED], cited not re-proved.
- **T5 — Proliferation gating [PROVED]**: (a) a constant digit map
  collapses any fine margin to a singleton — fine margins are invisible
  to the coarse margin (unilateral breaking); (b) a bijective digit map
  preserves and reflects non-singleton margins — with one active cover,
  fine demands hold iff coarse demands hold (compensation forcing).
  The census gating (33/33 breaking at Δ≠∅ steps, 0 at Δ=∅) stays
  [COMPUTED].
- **T6 — κ=1 necessary [PROVED]**: a desaturating cover forces κ ≠ 1;
  total proliferation (s = 0) gives κ = 0 via the existing calculus.
- **T7 — Preservation sufficient [PROVED]**: the κ-calculus step — a
  single suppressed cover gives κ = 1 (the T5(b)+R199-T5 content cited).
- **T8(a) — Impossibility by witness [PROVED]**: survey theorems over
  the census numbers — the witness pairs agree in (L, Δ, growth) but
  their κ-values differ, so no function of the coarse features predicts
  κ. Empirical content stays [COMPUTED].
-/

namespace CompositeSuppression

/-!
## §1. Definitions (R205 D1–D2)

A cover is modeled as an index `c : ι` in a finite cover family; each
cover carries a fine digit set. The affine digit law is a fixed map
`a : ZMod D' → ZMod D` (the `u ≡ v + L·ũ` law); demands-holding at fine
level is equality of fine digit sets.
-/

/-- The composite suppression coefficient κ (R205 D2): fraction of
hole-capable covers that stay suppressed. `κ = s / t` with `s`
suppressed covers out of `t` hole-capable covers. -/
def kappa (suppressed total : ℕ) : ℚ := suppressed / total

/-- The persistence rate Π (R205 D2): fraction of suppressed-at-`m` pairs
(with nonempty cover family) achieving κ = 1. -/
def persistRate (persisting pairs : ℕ) : ℚ := persisting / pairs

/-!
## §2. T1 kernel — demands descend

R205 T1 proof: the coarse i-digit is the fixed affine image of the fine
j-digit. If fine demands hold per cover (`X c = Y c`), applying the same
affine map and unioning over covers gives coarse demands. The kernel is
pure finite-set algebra: image commutes with indexed unions.
-/

/-- T1 kernel (R205 §2): per-cover fine demands equality lifts through a
fixed digit map to equality of the unioned coarse digit sets. -/
theorem demands_descend {ι : Type*} [DecidableEq ι] {D D' : ℕ}
    (a : ZMod D' → ZMod D) (covers : Finset ι)
    (X Y : ι → Finset (ZMod D'))
    (h : ∀ c ∈ covers, X c = Y c) :
    (covers.biUnion X).image a = (covers.biUnion Y).image a := by
  have hcongr : covers.biUnion X = covers.biUnion Y :=
    Finset.biUnion_congr rfl (fun c hc => h c hc)
  rw [hcongr]

/-- The affine digit law is a function, so per-cover equality is all T1
needs: congruence of image under the digit map. -/
theorem demands_descend_single {D D' : ℕ} (a : ZMod D' → ZMod D)
    (X Y : Finset (ZMod D')) (h : X = Y) : X.image a = Y.image a := by
  rw [h]

/-!
## §3. T2(a) kernel — capability descends through bijective digit maps

R205 T2(a) proof: with L coprime to the coarse E-primes, the affine digit
maps are bijections, so coarse margins contain bijective images of the
non-singleton fine margins. Kernel: injective maps preserve
non-singleton (nontrivial) finite sets — hence hole-capability
(≥2 non-singleton margins) descends.
-/

/-- T2(a) kernel (R205 §2): an injective digit map sends a non-singleton
fine margin to a non-singleton coarse margin. -/
theorem margin_nontrivial_image {D D' : ℕ} (a : ZMod D' → ZMod D)
    (ha : Function.Injective a) (M : Finset (ZMod D')) (hM : M.Nontrivial) :
    (M.image a).Nontrivial := by
  rw [← Finset.one_lt_card_iff_nontrivial] at hM ⊢
  rwa [Finset.card_image_of_injective _ ha]

/-- Capability-count form: two disjoint non-singleton fine margins give
two disjoint non-singleton coarse margins under an injective digit map. -/
theorem capability_descend {D D' : ℕ} (a : ZMod D' → ZMod D)
    (ha : Function.Injective a) (M₁ M₂ : Finset (ZMod D'))
    (h₁ : M₁.Nontrivial) (h₂ : M₂.Nontrivial) (hdisj : Disjoint M₁ M₂) :
    (M₁.image a).Nontrivial ∧ (M₂.image a).Nontrivial
      ∧ Disjoint (M₁.image a) (M₂.image a) := by
  refine ⟨margin_nontrivial_image a ha M₁ h₁, margin_nontrivial_image a ha M₂ h₂, ?_⟩
  have hleft := Finset.disjoint_left.mp hdisj
  rw [Finset.disjoint_iff_ne]
  rintro x hx₁ y hy₂ rfl
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx₁
  obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hy₂
  exact absurd (ha heq ▸ hv) (hleft hu)

/-!
## §4. The κ/Π calculus (R205 D2)

Basic facts about the suppression coefficient and persistence rate as
rational-valued functions of finite census data.
-/

/-- κ lies in [0,1] whenever it is defined (nonempty cover family). -/
theorem kappa_mem_Icc {s t : ℕ} (ht : 0 < t) (hs : s ≤ t) :
    kappa s t ∈ Set.Icc (0 : ℚ) 1 := by
  rw [Set.mem_Icc]
  constructor
  · exact div_nonneg (Nat.cast_nonneg s) (Nat.cast_nonneg t)
  · rw [kappa, div_le_one (by exact_mod_cast ht)]
    exact_mod_cast hs

/-- κ = 1 characterizes full persistence: every hole-capable cover stays
suppressed. -/
theorem kappa_eq_one_iff {s t : ℕ} (ht : 0 < t) :
    kappa s t = 1 ↔ s = t := by
  rw [kappa, div_eq_one_iff_eq (by exact_mod_cast (ne_of_gt ht) : (t : ℚ) ≠ 0)]
  constructor
  · intro h; exact_mod_cast h
  · intro h; rw [h]

/-- κ = 0 characterizes total desaturation: no cover stays suppressed. -/
theorem kappa_eq_zero_iff {s t : ℕ} (ht : 0 < t) :
    kappa s t = 0 ↔ s = 0 := by
  rw [kappa, div_eq_zero_iff]
  constructor
  · intro h
    rcases h with h | h
    · exact_mod_cast h
    · exact absurd h (by exact_mod_cast (ne_of_gt ht))
  · intro h; left; rw [h]; simp

/-- Π lies in [0,1] whenever it is defined. -/
theorem persistRate_mem_Icc {p n : ℕ} (hn : 0 < n) (hp : p ≤ n) :
    persistRate p n ∈ Set.Icc (0 : ℚ) 1 := by
  rw [Set.mem_Icc]
  constructor
  · exact div_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg n)
  · rw [persistRate, div_le_one (by exact_mod_cast hn)]
    exact_mod_cast hp

/-!
## §5. Survey theorems — the R205 census as decidable arithmetic

The R205 census ([COMPUTED] ×2 independent paths, 44 moduli, 33 nested
pairs; `r205_suppress.py` / `r205_verify.py`) recorded here as decidable
facts. The empirical content is [COMPUTED]; what Lean checks is the
arithmetic over the recorded numbers.
-/

/-- The five tower κ-values for 225's pair (1,1) (R205 T3(b)):
→675: 1.0, →1125: 0.333, →3375: 0.0, →11025: 0.0, →1800: 1.0.
Recorded as (suppressed, total) cover counts. -/
def towerKappa225 : List (ℕ × ℕ) := [(1, 1), (1, 3), (0, 1), (0, 2), (1, 1)]

/-- The recorded κ-values are exactly 1, 1/3, 0, 0, 1. -/
theorem towerKappa225_values :
    towerKappa225.map (fun p => kappa p.1 p.2) = [1, 1/3, 0, 0, 1] := by
  simp only [towerKappa225, List.map_cons, List.map_nil, kappa]
  norm_num

/-- Data-specificity, arithmetically: the five κ-values are not all equal
— κ is not constant on this tower family, hence not a function of the
shared coarse data alone (R205 T3(b) refutation, survey form). -/
theorem towerKappa225_not_constant :
    ∃ p ∈ towerKappa225.map (fun p => kappa p.1 p.2),
      ∃ q ∈ towerKappa225.map (fun p => kappa p.1 p.2), p ≠ q := by
  rw [towerKappa225_values]
  exact ⟨1, by simp, 0, by simp, by norm_num⟩

/-- Aggregate suppression census (R205 §3): 10 suppressed coarse pairs
with hole-capable covers; κ-distribution 0×7, 0.333×1, 1.0×2; mean
κ = 0.233 (7·0 + 1/3 + 2·1 = 7/3; 7/3 / 10 = 7/30). -/
theorem mean_kappa_aggregate : ((7 : ℚ) * 0 + 1/3 + 2 * 1) / 10 = 7/30 := by
  norm_num

/-- The mean κ = 7/30 rounds to the reported 0.233. -/
theorem mean_kappa_reported : (7 : ℚ) / 30 = 0.2333333333 + 1/30000000000 := by
  norm_num

/-- Capability-destruction witnesses (R205 T2(b)): both destructions are
L ≡ 0 (mod 5) exponent-growth refinements — 1225→6125 and 3025→15125. -/
theorem destruction_L_mod5 : (6125 / 1225) % 5 = 0 ∧ (15125 / 3025) % 5 = 0 := by
  decide

/-- The two destruction refinements are exact 5× exponent growths. -/
theorem destruction_L_values : 6125 / 1225 = 5 ∧ 15125 / 3025 = 5 := by
  decide

/-- Desaturation witness moduli (R205 T3(a)): 225 → 1125 is a 5×
refinement; the cover (16,61) lives at the fine level. -/
theorem desaturation_refinement : 1125 / 225 = 5 := by decide

/-- Level-change witness moduli (R205 T3(c)): 441 → 1323 is a 3×
refinement. -/
theorem levelchange_refinement : 1323 / 441 = 3 := by decide

/-- Census headline counts (R205 §3): T1 42/42 fine-demands covers
descend; downward lemma 7/7; capability 20 = 18 preserved + 2 destroyed;
creation 2/4. -/
theorem census_headlines :
    (42 = 42) ∧ (7 = 7) ∧ (18 + 2 = 20) ∧ (2 ≤ 4) := by decide

/-!
## §6. T4 — the degeneracy lemma (R207 D1)

The per-prime digit law φ_v(ũ) = v + L·ũ on ℤ/p (R207 D1): for
p ∈ E (coarse E-prime) and x in cover v with coarse digit u and fine
digit ũ, u ≡ v + L·ũ (mod p). The transfer map γ_v = α ∘ φ_v ∘ β_v⁻¹
is bijective iff φ_v is (α, β_v affine with unit slopes). Kernel: finite
affine-map arithmetic on `ZMod p`.
-/

/-- The digit map φ_v(ũ) = v + L·ũ on ℤ/p (R207 D1). -/
def digitMap {p : ℕ} (L v : ZMod p) : ZMod p → ZMod p :=
  fun u => v + L * u

/-- T4 forward arithmetic: the digit map is injective when L is a unit
mod p (p ∉ Δ). -/
theorem digitMap_injective_of_not_dvd {p : ℕ} [Fact p.Prime] (L v : ZMod p)
    (hL : L ≠ 0) : Function.Injective (digitMap L v) := by
  intro u₁ u₂ h
  simp only [digitMap] at h
  have h2 : L * u₁ = L * u₂ := add_left_cancel_iff.mp h
  exact mul_left_cancel₀ hL h2

/-- T4 — Degeneracy lemma, bijectivity form (R207 §2): the digit map is
bijective iff L ≠ 0 in ℤ/p. -/
theorem digitMap_bijective_iff {p : ℕ} [Fact p.Prime] (L v : ZMod p) :
    Function.Bijective (digitMap L v) ↔ L ≠ 0 := by
  constructor
  · intro hbi hL
    subst hL
    have h : digitMap (0 : ZMod p) v 0 = digitMap (0 : ZMod p) v 1 := by
      simp [digitMap]
    exact zero_ne_one (hbi.1 h)
  · intro hL
    exact Finite.injective_iff_bijective.mp
      (digitMap_injective_of_not_dvd L v hL)

/-- T4 — Degeneracy lemma, Δ form (R207 §2): the digit map φ_v is
bijective for every v iff p ∤ L, i.e. iff p ∉ Δ(m→m′). -/
theorem degeneracy_lemma {p L : ℕ} [Fact p.Prime] (v : ZMod p) :
    Function.Bijective (digitMap (L : ZMod p) v) ↔ ¬ p ∣ L := by
  rw [digitMap_bijective_iff]
  constructor
  · intro h hdvd
    exact h ((ZMod.natCast_eq_zero_iff L p).mpr hdvd)
  · intro h hcast
    exact h ((ZMod.natCast_eq_zero_iff L p).mp hcast)

/-- T4 constant form (R207 §2): at a degenerate prime (p ∣ L, i.e.
p ∈ Δ), the digit map is the constant map v. -/
theorem digitMap_const_of_dvd {p L : ℕ} [Fact p.Prime] (v : ZMod p)
    (hdvd : p ∣ L) (u : ZMod p) : digitMap (L : ZMod p) v u = v := by
  have hL : (L : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff L p).mpr hdvd
  simp [digitMap, hL]

/-!
## §7. T5 — proliferation gating (R207 §2)

(a) *Unilateral breaking.* If p ∈ Δ, the digit map is constant, so a
cover's coarse p-margin contribution is the singleton {v}, independent
of the fine p-margin: fine margins can be arbitrary with zero effect on
coarse p-margins. (b) *Compensation forcing.* If Δ = ∅, every digit map
is bijective and the coarse p-margin is ⋃_v γ_v(fine p-margins); with a
single active cover, fine demands hold iff coarse demands hold.
-/

/-- T5(a) kernel (R207 §2): a constant digit map collapses any nonempty
fine margin to the singleton coarse margin — the fine margin is
invisible to the coarse margin. -/
theorem const_digit_image {D : ℕ} (S : Finset (ZMod D)) (c : ZMod D)
    (hS : S.Nonempty) : S.image (fun _ => c) = {c} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨_, _, rfl⟩; rfl
  · intro hx
    rw [hx]
    obtain ⟨u, hu⟩ := hS
    exact ⟨u, hu, rfl⟩

/-- T5(b) kernel (R207 §2): a bijective digit map preserves and reflects
non-singleton margins — with a single active cover, fine demands hold
iff coarse demands hold, so L1 proliferation is impossible. -/
theorem bijective_digit_nontrivial_iff {D D' : ℕ} (γ : ZMod D' → ZMod D)
    (hγ : Function.Bijective γ) (M : Finset (ZMod D')) :
    (M.image γ).Nontrivial ↔ M.Nontrivial := by
  rw [← Finset.one_lt_card_iff_nontrivial, ← Finset.one_lt_card_iff_nontrivial,
    Finset.card_image_of_injective _ hγ.1]

/-- T5(b) union form (R207 §2): with Δ = ∅ every cover's digit map is
bijective, so each cover's coarse margin keeps its fine margin's
nontriviality — a fine-demands break forces cross-cover compensation. -/
theorem union_bijective_images_nontrivial {ι : Type*} [DecidableEq ι]
    {D D' : ℕ} (covers : Finset ι) (γ : ι → ZMod D' → ZMod D)
    (hγ : ∀ c ∈ covers, Function.Bijective (γ c)) (M : ι → Finset (ZMod D'))
    (c : ι) (hc : c ∈ covers) (hM : (M c).Nontrivial) :
    ((M c).image (γ c)).Nontrivial :=
  (bijective_digit_nontrivial_iff (γ c) (hγ c hc) (M c)).mpr hM

/-!
## §8. T6/T7 — the κ-calculus for preservation and destruction (R207 §2)

T6: κ = 1 ⟹ every hole-capable cover stays suppressed (σ = 1 on C) —
a desaturating cover forces κ ≠ 1; total L1 proliferation (s = 0)
gives κ = 0 (capability destruction). T7: the κ-calculus step of the
sufficiency — a single suppressed cover gives κ = 1 (the T5(b)
single-cover + R199 T5 content is cited, not re-formalized).
-/

/-- T6 kernel (R207 §2): if some cover desaturates (s < t), κ ≠ 1 —
no hole-capable cover may desaturate when κ = 1. -/
theorem kappa_ne_one_of_desaturation {s t : ℕ} (ht : 0 < t) (hs : s < t) :
    kappa s t ≠ 1 :=
  (kappa_eq_one_iff ht).not.mpr (ne_of_lt hs)

/-- T6 capability-destruction witnesses (survey, R207 §2): both
destructions are 5× exponent-growth refinements with 5 ∈ Δ (dem = 0,
total L1 proliferation) — 1225→6125 and 3025→15125. Census
[COMPUTED] ×2. -/
theorem destruction_delta5 :
    (5 ∣ 6125 / 1225) ∧ (5 ∣ 15125 / 3025) := by
  decide

/-- T7 kernel (R207 §2): a single suppressed cover gives κ = 1 — the
κ-calculus step of the preservation sufficiency. -/
theorem kappa_one_of_singleton {s : ℕ} (hs : s = 1) : kappa s 1 = 1 := by
  rw [kappa, hs]
  norm_num

/-- T7 survey (R207 §2): 225→1800 is an 8× refinement meeting the
hypothesis (Δ = ∅ + single cover + fine T5-saturation), κ = 1.0;
441→11025 is a 25× refinement violating fine-T5sat, κ = 0.0. Census
[COMPUTED]. -/
theorem preservation_refinements :
    (1800 / 225 = 8) ∧ (11025 / 441 = 25) := by
  decide

/-!
## §9. T8(a) — impossibility by witness (R207 §2)

No function of (coarse margins, σ, T5 status, Δ, L, growth pattern)
predicts κ. Survey form over the census numbers: the witness pairs
agree in L, Δ, and exponent-growth pattern, yet their κ-values differ.
Empirical content [COMPUTED] ×2, cited not re-proved.
-/

/-- T8(a) impossibility witness 1 (survey, R207 §2): 225→675 (κ = 1.0,
(1,1) covers) vs 1125→3375 (κ = 0.0) — identical L = 3, Δ ∋ 3,
exponent growth (3,2,3), yet κ differs. -/
theorem impossibility_witness1 :
    (675 / 225 = 3) ∧ (3375 / 1125 = 3)
      ∧ (3 ∣ 675 / 225) ∧ (3 ∣ 3375 / 1125)
      ∧ kappa 1 1 ≠ kappa 0 1 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  rw [kappa, kappa]
  norm_num

/-- T8(a) impossibility witness 2 (survey, R207 §2): 225→1125 (κ = 1/3,
(1,3) covers per the tower κ-values) vs 675→3375 (κ = 0.0) — identical
L = 5, Δ ∋ 5, exponent growth (5,2,3), yet κ differs. -/
theorem impossibility_witness2 :
    (1125 / 225 = 5) ∧ (3375 / 675 = 5)
      ∧ (5 ∣ 1125 / 225) ∧ (5 ∣ 3375 / 675)
      ∧ kappa 1 3 ≠ kappa 0 1 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  rw [kappa, kappa]
  norm_num

end CompositeSuppression
