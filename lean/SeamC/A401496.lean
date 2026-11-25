import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Seam C Entry S012 (OEIS A401496): Mwafise's Complement-Closed Riordan-Graph Recurrence

Formalizes and proves Arnauld Mesinga Mwafise's conjectured recurrence on `OEIS A401496`
(`%F` line 12, Oct 27 2026; live revision `#9`, Nov 04 2026 15:05:12) and `OEIS A401493`
(`%C` line 10, live revision `#10`, Nov 03 2026 17:02:17) against the frozen target contract
`PIN-S012.md` v1 (`delta_vs_source: NONE`), following the five-step closed-layer route from
`SCOPING-S012.md` (§2.1, Steps 1–5).
-/

namespace SeamC.A401496

open scoped BigOperators

/-! ### Pinned Target Definitions (`PIN-S012.md` v1) -/

/-- Labeled Riordan graph predicate (`OEIS A401493` `%C` line 10, 0-based on `Fin n` via
`I = i.val + 1`, `J = j.val + 1`): `G` arises from formal power series `g, f` over `GF(2)`
(`ZMod 2`) with `f(0) = 0` such that for `0 ≤ j < i < n`, `G.Adj i j` holds iff
`[t^(i - 1)] (g(t) * f(t)^j) = 1`. -/
def IsLabeledRiordanGraph (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ g f : PowerSeries (ZMod 2), PowerSeries.coeff 0 f = 0 ∧
    ∀ i j : Fin n, j.val < i.val → (G.Adj i j ↔ PowerSeries.coeff (i.val - 1) (g * f ^ j.val) = 1)

/-- `OEIS A401496(n)` (`%N` line 8): number of labeled Riordan graphs of order `n` whose graph
complement `Gᶜ` on the same vertex labeling `Fin n` is also a labeled Riordan graph. -/
noncomputable def complementClosedRiordanCount (n : ℕ) : ℕ :=
  Nat.card { G : SimpleGraph (Fin n) // IsLabeledRiordanGraph n G ∧ IsLabeledRiordanGraph n Gᶜ }

/-! ### Section 1: `ZMod 2` Arithmetic, `PowerSeries (ZMod 2)`, Frobenius Squaring, & `EqMod` -/

private abbrev PS := PowerSeries (ZMod 2)

private theorem zmod2_dichotomy (a : ZMod 2) : a = 0 ∨ a = 1 :=
  match a with
  | 0 => Or.inl rfl
  | 1 => Or.inr rfl

private theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> rfl

private theorem zmod2_neg (a : ZMod 2) : -a = a := by
  fin_cases a <;> rfl

private theorem zmod2_sq (a : ZMod 2) : a ^ 2 = a := by
  fin_cases a <;> rfl

private theorem zmod2_add_eq_zero_iff (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  rcases zmod2_dichotomy a with rfl | rfl <;> rcases zmod2_dichotomy b with rfl | rfl <;> decide

private theorem zmod2_eq_one_iff_eq (a b : ZMod 2) : (a = 1 ↔ b = 1) ↔ a = b := by
  rcases zmod2_dichotomy a with rfl | rfl <;> rcases zmod2_dichotomy b with rfl | rfl <;> decide

private theorem zmod2_not_eq_one_iff_one_add (a : ZMod 2) : ¬ a = 1 ↔ 1 + a = 1 := by
  rcases zmod2_dichotomy a with rfl | rfl <;> decide

private theorem zmod2_not_eq_one_iff_eq_zero (a : ZMod 2) : ¬ a = 1 ↔ a = 0 := by
  rcases zmod2_dichotomy a with rfl | rfl <;> decide

private theorem zmod2_ne_zero_iff_eq_one (a : ZMod 2) : a ≠ 0 ↔ a = 1 := by
  rcases zmod2_dichotomy a with rfl | rfl <;> decide

private theorem ps_add_self (p : PS) : p + p = 0 := by
  ext d
  simp [zmod2_add_self]

private theorem ps_neg (p : PS) : -p = p := by
  ext d
  rw [map_neg, zmod2_neg]

private theorem ps_sub_eq_add (p q : PS) : p - q = p + q := by
  rw [sub_eq_add_neg, ps_neg]

private theorem ps_add_sq (p q : PS) : (p + q) ^ 2 = p ^ 2 + q ^ 2 := by
  calc
    (p + q) ^ 2 = p ^ 2 + (p * q + p * q) + q ^ 2 := by ring
    _ = p ^ 2 + q ^ 2 := by rw [ps_add_self, add_zero]

/-- Frobenius coefficient squaring in `PowerSeries (ZMod 2)`:
`[t^m](h(t)^2) = [t^(m/2)] h(t)` when `m` is even and `0` when `m` is odd. -/
theorem coeff_sq_zmod2 : ∀ (m : ℕ) (h : PS),
    PowerSeries.coeff m (h ^ 2) = if m % 2 = 0 then PowerSeries.coeff (m / 2) h else 0
  | 0, h => by
    rw [sq, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← sq, zmod2_sq]
    simp
  | 1, h => by
    have hh := PowerSeries.eq_X_mul_shift_add_const h
    let h' : PS := PowerSeries.mk fun p => PowerSeries.coeff (p + 1) h
    have hsq : h ^ 2 = PowerSeries.X ^ 2 * h' ^ 2 + PowerSeries.C (PowerSeries.constantCoeff h) := by
      conv_lhs => rw [hh]
      rw [ps_add_sq, mul_pow, ← map_pow, zmod2_sq]
    rw [hsq, map_add, PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega : ¬ 2 ≤ 1),
      PowerSeries.coeff_C_of_ne_zero (by omega : (1 : ℕ) ≠ 0), add_zero]
    simp
  | m + 2, h => by
    have hh := PowerSeries.eq_X_mul_shift_add_const h
    let h' : PS := PowerSeries.mk fun p => PowerSeries.coeff (p + 1) h
    have hsq : h ^ 2 = PowerSeries.X ^ 2 * h' ^ 2 + PowerSeries.C (PowerSeries.constantCoeff h) := by
      conv_lhs => rw [hh]
      rw [ps_add_sq, mul_pow, ← map_pow, zmod2_sq]
    rw [hsq, map_add, PowerSeries.coeff_X_pow_mul (h' ^ 2) 2 m,
      PowerSeries.coeff_C_of_ne_zero (by omega : m + 2 ≠ 0), add_zero, coeff_sq_zmod2 m h']
    have hmod : (m + 2) % 2 = m % 2 := by omega
    have hdiv : (m + 2) / 2 = m / 2 + 1 := by omega
    rw [hmod, hdiv]
    split_ifs <;> simp [h']

/-- Geometric unit `u(t) = (1 + t)⁻¹ = ∑_{d ≥ 0} t^d` in `PowerSeries (ZMod 2)`. -/
noncomputable def uSeries : PS :=
  PowerSeries.mk fun _ => 1

@[simp]
theorem coeff_uSeries (d : ℕ) : PowerSeries.coeff d uSeries = 1 :=
  PowerSeries.coeff_mk d _

@[simp]
theorem constantCoeff_uSeries : PowerSeries.constantCoeff uSeries = 1 :=
  rfl

theorem one_add_X_mul_uSeries : (1 + PowerSeries.X : PS) * uSeries = 1 := by
  ext d
  rcases d with _ | d
  · simp
  · rw [add_mul, one_mul, map_add, PowerSeries.coeff_succ_X_mul, coeff_uSeries, coeff_uSeries,
      zmod2_add_self, PowerSeries.coeff_one, ite_eq_right (Nat.succ_ne_zero d)]

theorem coeff_uSeries_mul_X_pow (c r : ℕ) :
    PowerSeries.coeff r (uSeries * PowerSeries.X ^ c) = if c ≤ r then 1 else 0 := by
  rw [PowerSeries.coeff_mul_X_pow']
  split_ifs <;> simp

/-- Truncated `m`-jet congruence `p ≡ q (mod X^m)` over `PowerSeries (ZMod 2)`. -/
def EqMod (m : ℕ) (p q : PS) : Prop :=
  ∀ d < m, PowerSeries.coeff d p = PowerSeries.coeff d q

theorem eqMod_iff_X_pow_dvd (m : ℕ) (p q : PS) :
    EqMod m p q ↔ (PowerSeries.X : PS) ^ m ∣ (p + q) := by
  rw [PowerSeries.X_pow_dvd_iff, EqMod]
  refine forall₂_congr fun d _ => ?_
  rw [map_add, zmod2_add_eq_zero_iff]

theorem EqMod.refl (m : ℕ) (p : PS) : EqMod m p p :=
  fun _ _ => rfl

theorem EqMod.symm {m : ℕ} {p q : PS} (h : EqMod m p q) : EqMod m q p :=
  fun d hd => (h d hd).symm

theorem EqMod.trans {m : ℕ} {p q r : PS} (h1 : EqMod m p q) (h2 : EqMod m q r) : EqMod m p r :=
  fun d hd => (h1 d hd).trans (h2 d hd)

theorem EqMod.mono {m₁ m₂ : ℕ} {p q : PS} (hm : m₁ ≤ m₂) (h : EqMod m₂ p q) : EqMod m₁ p q :=
  fun d hd => h d (lt_of_lt_of_le hd hm)

theorem EqMod.add {m : ℕ} {p₁ q₁ p₂ q₂ : PS} (h1 : EqMod m p₁ q₁) (h2 : EqMod m p₂ q₂) :
    EqMod m (p₁ + p₂) (q₁ + q₂) := by
  intro d hd
  simp [h1 d hd, h2 d hd]

theorem EqMod.mul {m : ℕ} {p₁ q₁ p₂ q₂ : PS} (h1 : EqMod m p₁ q₁) (h2 : EqMod m p₂ q₂) :
    EqMod m (p₁ * p₂) (q₁ * q₂) := by
  rw [eqMod_iff_X_pow_dvd] at h1 h2 ⊢
  have hid : p₁ * p₂ + q₁ * q₂ = (p₁ + q₁) * p₂ + q₁ * (p₂ + q₂) := by
    calc
      p₁ * p₂ + q₁ * q₂ = p₁ * p₂ + (q₁ * p₂ + q₁ * p₂) + q₁ * q₂ := by
        rw [ps_add_self, add_zero]
      _ = (p₁ + q₁) * p₂ + q₁ * (p₂ + q₂) := by ring
  rw [hid]
  exact dvd_add (dvd_mul_of_dvd_left h1 p₂) (dvd_mul_of_dvd_right h2 q₁)

theorem EqMod.pow {m : ℕ} {p q : PS} (h : EqMod m p q) : ∀ c : ℕ, EqMod m (p ^ c) (q ^ c)
  | 0 => by simpa using EqMod.refl m 1
  | c + 1 => by
    rw [pow_succ, pow_succ]
    exact EqMod.mul (EqMod.pow h c) h

theorem EqMod.cancel_unit_left {m : ℕ} {φ p q : PS} (hφ : PowerSeries.coeff 0 φ = 1) :
    EqMod m (φ * p) (φ * q) ↔ EqMod m p q := by
  constructor
  · intro h
    have hconst : PowerSeries.constantCoeff φ = (1 : (ZMod 2)ˣ) := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hφ]
      rfl
    let ψ := PowerSeries.invOfUnit φ 1
    have hψ : ψ * φ = 1 := PowerSeries.invOfUnit_mul φ 1 hconst
    have hmul := EqMod.mul (EqMod.refl m ψ) h
    rwa [← mul_assoc, ← mul_assoc, hψ, one_mul, one_mul] at hmul
  · exact fun h => EqMod.mul (EqMod.refl m φ) h

theorem EqMod.cancel_unit_zero {m : ℕ} {φ p : PS} (hφ : PowerSeries.coeff 0 φ = 1) :
    EqMod m (φ * p) 0 ↔ EqMod m p 0 := by
  conv_lhs => rw [← mul_zero φ]
  exact EqMod.cancel_unit_left hφ

theorem EqMod.X_pow_mul_zero_iff (m r : ℕ) (p : PS) :
    EqMod m (PowerSeries.X ^ r * p) 0 ↔ EqMod (m - r) p 0 := by
  constructor
  · intro h d hd
    have hdr : d + r < m := by omega
    have hcoeff := h (d + r) hdr
    rwa [PowerSeries.coeff_X_pow_mul] at hcoeff
  · intro h d hd
    rw [PowerSeries.coeff_X_pow_mul']
    split_ifs with hrd
    · exact h (d - r) (by omega)
    · simp

theorem coeff_mul_pow_eq_zero_of_lt {g f : PS} (hf0 : PowerSeries.coeff 0 f = 0)
    {r c : ℕ} (hrc : r < c) : PowerSeries.coeff r (g * f ^ c) = 0 := by
  have hXdvd : (PowerSeries.X : PS) ∣ f := by
    rw [PowerSeries.X_dvd_iff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hf0
  have hdvd : (PowerSeries.X : PS) ^ c ∣ g * f ^ c :=
    dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hXdvd c) g
  exact (PowerSeries.X_pow_dvd_iff.mp hdvd) r hrc

/-! ### Step 1 (`SCOPING-S012.md` §2.1): Graph Realization & `m`-Jet Column Equivalence -/

/-- Explicit labeled graph on `Fin n` determined by `(g, f) ∈ PowerSeries (ZMod 2)²`. -/
def riordanGraph (n : ℕ) (g f : PS) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j : Fin n =>
    j.val < i.val ∧ PowerSeries.coeff (i.val - 1) (g * f ^ j.val) = 1

theorem riordanGraph_adj_of_lt {n : ℕ} (g f : PS) {i j : Fin n} (hij : j.val < i.val) :
    (riordanGraph n g f).Adj i j ↔ PowerSeries.coeff (i.val - 1) (g * f ^ j.val) = 1 := by
  rw [riordanGraph, SimpleGraph.fromRel_adj]
  have hne : i ≠ j := fun h => by rw [h] at hij; exact Nat.lt_irrefl _ hij
  have hnot : ¬ i.val < j.val := by omega
  simp [hne, hij, hnot]

theorem eq_riordanGraph_of_spec {n : ℕ} {G : SimpleGraph (Fin n)} {g f : PS}
    (hspec : ∀ i j : Fin n, j.val < i.val →
      (G.Adj i j ↔ PowerSeries.coeff (i.val - 1) (g * f ^ j.val) = 1)) :
    G = riordanGraph n g f := by
  ext u v
  rcases lt_trichotomy v.val u.val with hlt | heq | hgt
  · rw [hspec u v hlt, riordanGraph_adj_of_lt g f hlt]
  · have huv : u = v := Fin.ext heq.symm
    subst huv
    simp
  · rw [G.adj_comm, (riordanGraph n g f).adj_comm, hspec v u hgt, riordanGraph_adj_of_lt g f hgt]

theorem isLabeledRiordanGraph_iff_exists_eq (n : ℕ) (G : SimpleGraph (Fin n)) :
    IsLabeledRiordanGraph n G ↔
      ∃ g f : PS, PowerSeries.coeff 0 f = 0 ∧ G = riordanGraph n g f := by
  constructor
  · rintro ⟨g, f, hf0, hspec⟩
    exact ⟨g, f, hf0, eq_riordanGraph_of_spec hspec⟩
  · rintro ⟨g, f, hf0, rfl⟩
    exact ⟨g, f, hf0, fun _ _ hij => riordanGraph_adj_of_lt g f hij⟩

theorem riordanGraph_isLabeled {n : ℕ} {g f : PS} (hf0 : PowerSeries.coeff 0 f = 0) :
    IsLabeledRiordanGraph n (riordanGraph n g f) :=
  (isLabeledRiordanGraph_iff_exists_eq n _).mpr ⟨g, f, hf0, rfl⟩

/-- Step 1 column equivalence: for `f₁(0) = f₂(0) = 0`, `G_n(g₁, f₁) = G_n(g₂, f₂)` iff
all `m`-jet columns `g₁ f₁^c ≡ g₂ f₂^c (mod X^(n - 1))` agree for `0 ≤ c < n - 1`. -/
theorem riordanGraph_eq_iff {n : ℕ} {g₁ f₁ g₂ f₂ : PS}
    (hf₁ : PowerSeries.coeff 0 f₁ = 0) (hf₂ : PowerSeries.coeff 0 f₂ = 0) :
    riordanGraph n g₁ f₁ = riordanGraph n g₂ f₂ ↔
      ∀ c < n - 1, EqMod (n - 1) (g₁ * f₁ ^ c) (g₂ * f₂ ^ c) := by
  constructor
  · intro heq c hc r hr
    rcases lt_or_ge r c with hrc | hcr
    · rw [coeff_mul_pow_eq_zero_of_lt hf₁ hrc, coeff_mul_pow_eq_zero_of_lt hf₂ hrc]
    · let i : Fin n := ⟨r + 1, by omega⟩
      let j : Fin n := ⟨c, by omega⟩
      have hij : j.val < i.val := by simp [i, j]; omega
      have hadj : (riordanGraph n g₁ f₁).Adj i j ↔ (riordanGraph n g₂ f₂).Adj i j := by
        rw [heq]
      rw [riordanGraph_adj_of_lt g₁ f₁ hij, riordanGraph_adj_of_lt g₂ f₂ hij] at hadj
      simpa [i, j, zmod2_eq_one_iff_eq] using hadj
  · intro hcols
    apply eq_riordanGraph_of_spec
    intro i j hij
    rw [riordanGraph_adj_of_lt g₁ f₁ hij]
    have hc : j.val < n - 1 := by omega
    have hr : i.val - 1 < n - 1 := by omega
    rw [hcols j.val hc (i.val - 1) hr]

/-! ### Step 3 (`SCOPING-S012.md` §2.1): Complementation as Appell Translation & `g₀ = 0` Doubling -/

theorem compl_eq_riordanGraph_iff {n : ℕ} {g f g' f' : PS}
    (hf0 : PowerSeries.coeff 0 f = 0) (hf'0 : PowerSeries.coeff 0 f' = 0) :
    (riordanGraph n g f)ᶜ = riordanGraph n g' f' ↔
      ∀ c < n - 1, EqMod (n - 1) (g' * f' ^ c) (uSeries * PowerSeries.X ^ c + g * f ^ c) := by
  constructor
  · intro heq c hc r hr
    rcases lt_or_ge r c with hrc | hcr
    · rw [coeff_mul_pow_eq_zero_of_lt hf'0 hrc, map_add, coeff_uSeries_mul_X_pow,
        ite_eq_right (by omega : ¬ c ≤ r), coeff_mul_pow_eq_zero_of_lt hf0 hrc, add_zero]
    · let i : Fin n := ⟨r + 1, by omega⟩
      let j : Fin n := ⟨c, by omega⟩
      have hij : j.val < i.val := by simp [i, j]; omega
      have hne : i ≠ j := fun h => by rw [h] at hij; exact Nat.lt_irrefl _ hij
      have hadj : (riordanGraph n g f)ᶜ.Adj i j ↔ (riordanGraph n g' f').Adj i j := by
        rw [heq]
      rw [SimpleGraph.compl_adj, and_iff_right hne, riordanGraph_adj_of_lt g f hij,
        zmod2_not_eq_one_iff_one_add, riordanGraph_adj_of_lt g' f' hij] at hadj
      have hu : PowerSeries.coeff r (uSeries * PowerSeries.X ^ c + g * f ^ c) =
          1 + PowerSeries.coeff r (g * f ^ c) := by
        rw [map_add, coeff_uSeries_mul_X_pow, ite_eq_left hcr]
      rw [hu]
      exact (zmod2_eq_one_iff_eq _ _).mp (by simpa [i, j] using hadj.symm)
  · intro hcols
    apply eq_riordanGraph_of_spec
    intro i j hij
    have hne : i ≠ j := fun h => by rw [h] at hij; exact Nat.lt_irrefl _ hij
    rw [SimpleGraph.compl_adj, and_iff_right hne, riordanGraph_adj_of_lt g f hij,
      zmod2_not_eq_one_iff_one_add]
    have hc : j.val < n - 1 := by omega
    have hr : i.val - 1 < n - 1 := by omega
    have hcr : j.val ≤ i.val - 1 := by omega
    rw [hcols j.val hc (i.val - 1) hr, map_add, coeff_uSeries_mul_X_pow, ite_eq_left hcr]

theorem compl_isLabeledRiordan_iff {n : ℕ} {g f : PS} (hf0 : PowerSeries.coeff 0 f = 0) :
    IsLabeledRiordanGraph n (riordanGraph n g f)ᶜ ↔
      ∃ g' f' : PS, PowerSeries.coeff 0 f' = 0 ∧
        ∀ c < n - 1, EqMod (n - 1) (g' * f' ^ c) (uSeries * PowerSeries.X ^ c + g * f ^ c) := by
  rw [isLabeledRiordanGraph_iff_exists_eq]
  refine exists_congr fun g' => exists_congr fun f' => and_congr_right fun hf'0 => ?_
  exact compl_eq_riordanGraph_iff hf0 hf'0

private abbrev CCSet (n : ℕ) : Type :=
  { G : SimpleGraph (Fin n) // IsLabeledRiordanGraph n G ∧ IsLabeledRiordanGraph n Gᶜ }

private abbrev CCSetZero (n : ℕ) (hn : 2 ≤ n) : Type :=
  { G : SimpleGraph (Fin n) //
      ¬ G.Adj ⟨1, by omega⟩ ⟨0, by omega⟩ ∧ IsLabeledRiordanGraph n G ∧ IsLabeledRiordanGraph n Gᶜ }

/-- Step 3 free involution `G ↦ Gᶜ` swapping `¬ G.Adj 1 0` (`g₀ = 0`) and `G.Adj 1 0` (`g₀ = 1`)
for every `n ≥ 2`. -/
noncomputable def complDoubleEquiv {n : ℕ} (hn : 2 ≤ n) :
    CCSetZero n hn ⊕ CCSetZero n hn ≃ CCSet n := by
  classical
  let v0 : Fin n := ⟨0, by omega⟩
  let v1 : Fin n := ⟨1, by omega⟩
  have hv10 : v1 ≠ v0 := by simp [v0, v1]
  refine
    { toFun := fun s =>
        match s with
        | Sum.inl ⟨G, _, hG, hGc⟩ => ⟨G, hG, hGc⟩
        | Sum.inr ⟨G, _, hG, hGc⟩ => ⟨Gᶜ, hGc, by simpa only [compl_compl] using hG⟩
      invFun := fun ⟨G, hG, hGc⟩ =>
        if h1 : G.Adj v1 v0 then
          Sum.inr ⟨Gᶜ, by rw [SimpleGraph.compl_adj]; exact fun h => h.2 h1,
            hGc, by simpa only [compl_compl] using hG⟩
        else
          Sum.inl ⟨G, h1, hG, hGc⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro (⟨G, h0, hG, hGc⟩ | ⟨G, h0, hG, hGc⟩)
    · simp [v0, v1, h0]
    · have hcadj : Gᶜ.Adj v1 v0 := (SimpleGraph.compl_adj G v1 v0).mpr ⟨hv10, h0⟩
      simp [v0, v1, hcadj]
  · rintro ⟨G, hG, hGc⟩
    by_cases h1 : G.Adj v1 v0 <;> simp [v0, v1, h1]

theorem riordanGraph_not_adj_one_zero_iff {n : ℕ} (hn : 2 ≤ n) (g f : PS) :
    ¬ (riordanGraph n g f).Adj ⟨1, by omega⟩ ⟨0, by omega⟩ ↔ PowerSeries.coeff 0 g = 0 := by
  have hlt : (⟨0, by omega⟩ : Fin n).val < (⟨1, by omega⟩ : Fin n).val := by simp
  rw [riordanGraph_adj_of_lt g f hlt]
  simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
    zmod2_not_eq_one_iff_eq_zero (PowerSeries.coeff 0 g)

/-! ### Step 4 (`SCOPING-S012.md` §2.1): Master Characterization Lemma on `g₀ = 0` -/

private theorem delta_identity (u g f : PS) :
    (u + g) * (u * PowerSeries.X ^ 2 + g * f ^ 2) + (u * PowerSeries.X + g * f) ^ 2 =
      u * (g * (f + PowerSeries.X) ^ 2) := by
  have h1 : (u * PowerSeries.X + g * f) ^ 2 = u ^ 2 * PowerSeries.X ^ 2 + g ^ 2 * f ^ 2 := by
    rw [ps_add_sq, mul_pow, mul_pow]
  have h2 : (f + PowerSeries.X) ^ 2 = f ^ 2 + PowerSeries.X ^ 2 := ps_add_sq f PowerSeries.X
  rw [h1, h2]
  calc
    (u + g) * (u * PowerSeries.X ^ 2 + g * f ^ 2) + (u ^ 2 * PowerSeries.X ^ 2 + g ^ 2 * f ^ 2)
      = (u ^ 2 * PowerSeries.X ^ 2 + u ^ 2 * PowerSeries.X ^ 2) +
          (g ^ 2 * f ^ 2 + g ^ 2 * f ^ 2) + u * (g * (f ^ 2 + PowerSeries.X ^ 2)) := by ring
    _ = u * (g * (f ^ 2 + PowerSeries.X ^ 2)) := by
      rw [ps_add_self, ps_add_self, zero_add, zero_add]

private theorem xnum_sq_identity (u g f : PS) :
    (u * PowerSeries.X + g * f) ^ 2 =
      (u + g) * (PowerSeries.X + f) * (u * PowerSeries.X + g * f) +
        (u + g) ^ 2 * PowerSeries.X * f + u * (g * (f + PowerSeries.X) ^ 2) := by
  have h1 : (u * PowerSeries.X + g * f) ^ 2 = u ^ 2 * PowerSeries.X ^ 2 + g ^ 2 * f ^ 2 := by
    rw [ps_add_sq, mul_pow, mul_pow]
  have h2 : (u + g) ^ 2 = u ^ 2 + g ^ 2 := ps_add_sq u g
  have h3 : (f + PowerSeries.X) ^ 2 = f ^ 2 + PowerSeries.X ^ 2 := ps_add_sq f PowerSeries.X
  rw [h1, h2, h3]
  calc
    u ^ 2 * PowerSeries.X ^ 2 + g ^ 2 * f ^ 2
      = u ^ 2 * PowerSeries.X ^ 2 + g ^ 2 * f ^ 2 +
          (u ^ 2 * PowerSeries.X * f + u ^ 2 * PowerSeries.X * f) +
          (g ^ 2 * PowerSeries.X * f + g ^ 2 * PowerSeries.X * f) +
          (u * g * f ^ 2 + u * g * f ^ 2) +
          (u * g * PowerSeries.X ^ 2 + u * g * PowerSeries.X ^ 2) +
          (u * g * PowerSeries.X * f + u * g * PowerSeries.X * f) := by
        simp [ps_add_self]
    _ = (u + g) * (PowerSeries.X + f) * (u * PowerSeries.X + g * f) +
          (u ^ 2 + g ^ 2) * PowerSeries.X * f + u * (g * (f ^ 2 + PowerSeries.X ^ 2)) := by ring

/-- Master Characterization Lemma (`SCOPING-S012.md` §2.1 Step 4):
For `n ≥ 2` and `(g, f)` with `f(0) = 0` and `g(0) = 0`, the complement `G_n(g, f)ᶜ` is a labeled
Riordan graph on `Fin n` iff `g(t) * (f(t) + t)^2 ≡ 0 (mod t^(n - 1))`. -/
theorem master_characterization_on_g0_zero {n : ℕ} {g f : PS}
    (hf0 : PowerSeries.coeff 0 f = 0) (hg0 : PowerSeries.coeff 0 g = 0) :
    IsLabeledRiordanGraph n (riordanGraph n g f)ᶜ ↔
      EqMod (n - 1) (g * (f + PowerSeries.X) ^ 2) 0 := by
  let m := n - 1
  rw [compl_isLabeledRiordan_iff hf0]
  constructor
  · rintro ⟨g', f', _, hcols⟩
    rcases le_or_gt m 2 with hm2 | hm3
    · have hgX : (PowerSeries.X : PS) ∣ g := by
        rw [PowerSeries.X_dvd_iff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
        exact hg0
      have hfX : (PowerSeries.X : PS) ∣ (f + PowerSeries.X) := by
        rw [PowerSeries.X_dvd_iff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, map_add,
          hf0, PowerSeries.coeff_zero_X, add_zero]
      have hdvd3 : (PowerSeries.X : PS) ^ 3 ∣ g * (f + PowerSeries.X) ^ 2 := by
        rw [show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one]
        exact mul_dvd_mul hgX (pow_dvd_pow_of_dvd hfX 2)
      have hmod3 : EqMod 3 (g * (f + PowerSeries.X) ^ 2) 0 := by
        rw [eqMod_iff_X_pow_dvd, add_zero]
        exact hdvd3
      exact EqMod.mono (by omega : m ≤ 3) hmod3
    · have h0 : EqMod m g' (uSeries + g) := by
        simpa using hcols 0 (by omega)
      have h1 : EqMod m (g' * f') (uSeries * PowerSeries.X + g * f) := by
        simpa using hcols 1 (by omega)
      have h2 : EqMod m (g' * f' ^ 2) (uSeries * PowerSeries.X ^ 2 + g * f ^ 2) :=
        hcols 2 hm3
      have h2g : EqMod m (g' * (g' * f' ^ 2)) ((uSeries + g) * (uSeries * PowerSeries.X ^ 2 + g * f ^ 2)) :=
        EqMod.mul h0 h2
      have h1sq : EqMod m ((g' * f') ^ 2) ((uSeries * PowerSeries.X + g * f) ^ 2) :=
        EqMod.pow h1 2
      have hg_eq : g' * (g' * f' ^ 2) = (g' * f') ^ 2 := by ring
      rw [hg_eq] at h2g
      have hrel : EqMod m ((uSeries + g) * (uSeries * PowerSeries.X ^ 2 + g * f ^ 2))
          ((uSeries * PowerSeries.X + g * f) ^ 2) :=
        (EqMod.symm h2g).trans h1sq
      have hsum := EqMod.add hrel (EqMod.refl m ((uSeries * PowerSeries.X + g * f) ^ 2))
      rw [ps_add_self, delta_identity] at hsum
      have hmul := EqMod.mul (EqMod.refl m (1 + PowerSeries.X)) hsum
      rwa [← mul_assoc, one_add_X_mul_uSeries, one_mul, mul_zero] at hmul
  · intro hΔ0
    let g' : PS := uSeries + g
    have hg'0 : PowerSeries.coeff 0 g' = 1 := by
      rw [map_add, coeff_uSeries, hg0, add_zero]
    have hg'const : PowerSeries.constantCoeff g' = (1 : (ZMod 2)ˣ) := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hg'0]
      rfl
    let g'Inv : PS := PowerSeries.invOfUnit g' 1
    have hg'_mul_inv : g' * g'Inv = 1 := PowerSeries.mul_invOfUnit g' 1 hg'const
    have hinv_mul_g' : g'Inv * g' = 1 := PowerSeries.invOfUnit_mul g' 1 hg'const
    let xNum : PS := uSeries * PowerSeries.X + g * f
    let f' : PS := g'Inv * xNum
    have hxNum0 : PowerSeries.coeff 0 xNum = 0 := by
      have hfX : (PowerSeries.X : PS) ∣ f := by
        rw [PowerSeries.X_dvd_iff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
        exact hf0
      have hdvd : (PowerSeries.X : PS) ∣ xNum :=
        dvd_add (dvd_mul_left PowerSeries.X uSeries) (dvd_mul_of_dvd_right hfX g)
      rwa [PowerSeries.X_dvd_iff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply] at hdvd
    have hf'0 : PowerSeries.coeff 0 f' = 0 := by
      have hxX : (PowerSeries.X : PS) ∣ xNum := by
        rw [PowerSeries.X_dvd_iff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
        exact hxNum0
      have hdvd : (PowerSeries.X : PS) ∣ f' := dvd_mul_of_dvd_right hxX g'Inv
      rwa [PowerSeries.X_dvd_iff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply] at hdvd
    refine ⟨g', f', hf'0, ?_⟩
    let Δ : PS := uSeries * (g * (f + PowerSeries.X) ^ 2)
    let S : PS := g' * (PowerSeries.X + f)
    let P : PS := g' ^ 2 * PowerSeries.X * f
    let W : ℕ → PS := fun k => g' ^ k * (uSeries * PowerSeries.X ^ (k + 1) + g * f ^ (k + 1))
    let Y : ℕ → PS := fun k => W k + xNum ^ (k + 1)
    have hY_dvd : ∀ k : ℕ, Δ ∣ Y k := by
      intro k
      induction k using Nat.strongRecOn with
      | ind k ih =>
        match k with
        | 0 =>
          have hY0 : Y 0 = 0 := by
            simp only [Y, W, zero_add, pow_zero, pow_one, one_mul, xNum]
            exact ps_add_self _
          rw [hY0]
          exact dvd_zero Δ
        | 1 =>
          have hY1 : Y 1 = Δ := by
            simp only [Y, W, pow_one, g', xNum, Δ]
            exact delta_identity uSeries g f
          rw [hY1]
        | k + 2 =>
          have hW_rec : W (k + 2) = S * W (k + 1) + P * W k := by
            simp only [W, S, P]
            rw [show g' ^ (k + 2) = g' ^ k * g' ^ 2 from pow_add g' k 2,
              show g' ^ (k + 1) = g' ^ k * g' from pow_succ g' k,
              show (PowerSeries.X : PS) ^ (k + 3) = PowerSeries.X ^ (k + 1) * PowerSeries.X ^ 2 from
                pow_add PowerSeries.X (k + 1) 2,
              show (PowerSeries.X : PS) ^ (k + 2) = PowerSeries.X ^ (k + 1) * PowerSeries.X from
                pow_succ PowerSeries.X (k + 1),
              show f ^ (k + 3) = f ^ (k + 1) * f ^ 2 from pow_add f (k + 1) 2,
              show f ^ (k + 2) = f ^ (k + 1) * f from pow_succ f (k + 1)]
            let gk := g' ^ k
            let xk := (PowerSeries.X : PS) ^ (k + 1)
            let fk := f ^ (k + 1)
            change gk * g' ^ 2 * (uSeries * (xk * PowerSeries.X ^ 2) + g * (fk * f ^ 2)) =
              g' * (PowerSeries.X + f) * (gk * g' * (uSeries * (xk * PowerSeries.X) + g * (fk * f))) +
                g' ^ 2 * PowerSeries.X * f * (gk * (uSeries * xk + g * fk))
            calc
              gk * g' ^ 2 * (uSeries * (xk * PowerSeries.X ^ 2) + g * (fk * f ^ 2))
                = gk * g' ^ 2 * (uSeries * (xk * PowerSeries.X ^ 2) + g * (fk * f ^ 2)) +
                    (gk * g' ^ 2 * uSeries * xk * PowerSeries.X * f +
                      gk * g' ^ 2 * uSeries * xk * PowerSeries.X * f) +
                    (gk * g' ^ 2 * g * fk * PowerSeries.X * f +
                      gk * g' ^ 2 * g * fk * PowerSeries.X * f) := by
                  simp [ps_add_self]
              _ = g' * (PowerSeries.X + f) * (gk * g' * (uSeries * (xk * PowerSeries.X) + g * (fk * f))) +
                    g' ^ 2 * PowerSeries.X * f * (gk * (uSeries * xk + g * fk)) := by ring
          have hx_rec : xNum ^ (k + 3) = S * xNum ^ (k + 2) + P * xNum ^ (k + 1) + Δ * xNum ^ (k + 1) := by
            have hx2 : xNum ^ 2 = S * xNum + P + Δ := xnum_sq_identity uSeries g f
            calc
              xNum ^ (k + 3) = xNum ^ 2 * xNum ^ (k + 1) := by rw [pow_add]; ring
              _ = (S * xNum + P + Δ) * xNum ^ (k + 1) := by rw [hx2]
              _ = S * (xNum * xNum ^ (k + 1)) + P * xNum ^ (k + 1) + Δ * xNum ^ (k + 1) := by ring
              _ = S * xNum ^ (k + 2) + P * xNum ^ (k + 1) + Δ * xNum ^ (k + 1) := by
                rw [← pow_succ']
          have hY_rec : Y (k + 2) = S * Y (k + 1) + P * Y k + Δ * xNum ^ (k + 1) := by
            change W (k + 2) + xNum ^ (k + 3) =
              S * (W (k + 1) + xNum ^ (k + 2)) + P * (W k + xNum ^ (k + 1)) + Δ * xNum ^ (k + 1)
            rw [hW_rec, hx_rec]
            ring
          rw [hY_rec]
          exact dvd_add
            (dvd_add (dvd_mul_of_dvd_right (ih (k + 1) (by omega)) S)
              (dvd_mul_of_dvd_right (ih k (by omega)) P))
            (dvd_mul_right Δ _)
    have hΔ_mod : (PowerSeries.X : PS) ^ m ∣ Δ := by
      have hXdvd : (PowerSeries.X : PS) ^ m ∣ g * (f + PowerSeries.X) ^ 2 := by
        simpa [eqMod_iff_X_pow_dvd] using hΔ0
      exact dvd_mul_of_dvd_right hXdvd uSeries
    intro c _hc
    rcases c with _ | k
    · simp [g', EqMod.refl]
    · have hY_mod : EqMod m (W k) (xNum ^ (k + 1)) := by
        rw [eqMod_iff_X_pow_dvd]
        exact dvd_trans hΔ_mod (hY_dvd k)
      have hmul := EqMod.mul (EqMod.refl m (g'Inv ^ k)) hY_mod
      have hlhs : g'Inv ^ k * W k = uSeries * PowerSeries.X ^ (k + 1) + g * f ^ (k + 1) := by
        simp only [W, ← mul_assoc, ← mul_pow, hinv_mul_g', one_pow, one_mul]
      have hrhs : g'Inv ^ k * xNum ^ (k + 1) = g' * f' ^ (k + 1) := by
        have h1 : g' * f' = xNum := by
          simp only [f', ← mul_assoc, hg'_mul_inv, one_mul]
        calc
          g'Inv ^ k * xNum ^ (k + 1)
            = g'Inv ^ k * (g' * f') ^ (k + 1) := by rw [h1]
          _ = g'Inv ^ k * ((g' ^ k * g') * f' ^ (k + 1)) := by rw [mul_pow, pow_succ]
          _ = (g'Inv ^ k * g' ^ k) * (g' * f' ^ (k + 1)) := by ring
          _ = (g'Inv * g') ^ k * (g' * f' ^ (k + 1)) := by rw [← mul_pow g'Inv g' k]
          _ = g' * f' ^ (k + 1) := by rw [hinv_mul_g', one_pow, one_mul]
      rw [hlhs, hrhs] at hmul
      exact EqMod.symm hmul

/-! ### Step 2 (`SCOPING-S012.md` §2.1): Canonical Parameterization & `A047849` Sanity Check -/

/-- Unit factor `1 + ∑_{j < k} b_j X^(j+1)` for a valuation-`r` canonical series `g = X^r * v`. -/
noncomputable def vOfBits {k : ℕ} (b : Fin k → ZMod 2) : PS :=
  PowerSeries.mk fun d =>
    if d = 0 then 1
    else if h : d - 1 < k then b ⟨d - 1, h⟩
    else 0

/-- Canonical `f = ∑_{j < k} b_j X^(j+1)` of degree `≤ k` with `f(0) = 0`. -/
noncomputable def fOfBits {k : ℕ} (b : Fin k → ZMod 2) : PS :=
  PowerSeries.mk fun d =>
    if d = 0 then 0
    else if h : d - 1 < k then b ⟨d - 1, h⟩
    else 0

@[simp]
theorem constantCoeff_vOfBits {k : ℕ} (b : Fin k → ZMod 2) :
    PowerSeries.constantCoeff (vOfBits b) = 1 :=
  rfl

theorem coeff_zero_vOfBits {k : ℕ} (b : Fin k → ZMod 2) :
    PowerSeries.coeff 0 (vOfBits b) = 1 := by
  simp [vOfBits]

theorem coeff_succ_vOfBits_of_lt {k : ℕ} (b : Fin k → ZMod 2) (j : Fin k) :
    PowerSeries.coeff (j.val + 1) (vOfBits b) = b j := by
  simp [vOfBits, j.isLt]

@[simp]
theorem constantCoeff_fOfBits {k : ℕ} (b : Fin k → ZMod 2) :
    PowerSeries.constantCoeff (fOfBits b) = 0 :=
  rfl

theorem coeff_zero_fOfBits {k : ℕ} (b : Fin k → ZMod 2) :
    PowerSeries.coeff 0 (fOfBits b) = 0 := by
  simp [fOfBits]

theorem coeff_succ_fOfBits_of_lt {k : ℕ} (b : Fin k → ZMod 2) (j : Fin k) :
    PowerSeries.coeff (j.val + 1) (fOfBits b) = b j := by
  simp [fOfBits, j.isLt]

/-- Canonical parameter space for all `L(n) = (4^(n-1) + 2)/3` labeled Riordan graphs of order `n`:
`Unit` (`(0, 0)`) plus layers `k : Fin (n - 1)` of valuation `r = n - 2 - k`. -/
abbrev CanonParam (n : ℕ) : Type :=
  Unit ⊕ Σ k : Fin (n - 1), (Fin k.val → ZMod 2) × (Fin k.val → ZMod 2)

noncomputable def evalCanonParam (n : ℕ) : CanonParam n → PS × PS
  | Sum.inl () => (0, 0)
  | Sum.inr ⟨k, (gb, fb)⟩ =>
      (PowerSeries.X ^ (n - 2 - k.val) * vOfBits gb, fOfBits fb)

theorem evalCanonParam_coeff_zero_snd (n : ℕ) (p : CanonParam n) :
    PowerSeries.coeff 0 (evalCanonParam n p).2 = 0 := by
  rcases p with ⟨⟩ | ⟨k, gb, fb⟩ <;> simp [evalCanonParam]

noncomputable def graphOfCanonParam (n : ℕ) (p : CanonParam n) :
    { G : SimpleGraph (Fin n) // IsLabeledRiordanGraph n G } :=
  ⟨riordanGraph n (evalCanonParam n p).1 (evalCanonParam n p).2,
    riordanGraph_isLabeled (evalCanonParam_coeff_zero_snd n p)⟩

theorem graphOfCanonParam_injective (n : ℕ) : Function.Injective (graphOfCanonParam n) := by
  intro p₁ p₂ heq
  have hG : riordanGraph n (evalCanonParam n p₁).1 (evalCanonParam n p₁).2 =
      riordanGraph n (evalCanonParam n p₂).1 (evalCanonParam n p₂).2 :=
    Subtype.mk.inj heq
  have hcols := (riordanGraph_eq_iff
    (evalCanonParam_coeff_zero_snd n p₁) (evalCanonParam_coeff_zero_snd n p₂)).mp hG
  rcases p₁ with ⟨⟩ | ⟨k₁, gb₁, fb₁⟩ <;> rcases p₂ with ⟨⟩ | ⟨k₂, gb₂, fb₂⟩
  · rfl
  · exfalso
    have hr₂ : n - 2 - k₂.val < n - 1 := by have := k₂.isLt; omega
    have h0 := hcols 0 (by have := k₂.isLt; omega) (n - 2 - k₂.val) hr₂
    simp only [evalCanonParam, pow_zero, mul_one, map_zero, PowerSeries.coeff_X_pow_mul',
      le_rfl, ite_true, tsub_self, PowerSeries.coeff_zero_eq_constantCoeff,
      constantCoeff_vOfBits] at h0
    exact zero_ne_one h0
  · exfalso
    have hr₁ : n - 2 - k₁.val < n - 1 := by have := k₁.isLt; omega
    have h0 := hcols 0 (by have := k₁.isLt; omega) (n - 2 - k₁.val) hr₁
    simp only [evalCanonParam, pow_zero, mul_one, map_zero, PowerSeries.coeff_X_pow_mul',
      le_rfl, ite_true, tsub_self, PowerSeries.coeff_zero_eq_constantCoeff,
      constantCoeff_vOfBits] at h0
    exact one_ne_zero h0
  · have hc0 := hcols 0 (by have := k₁.isLt; omega)
    simp only [evalCanonParam, pow_zero, mul_one] at hc0
    let r₁ := n - 2 - k₁.val
    let r₂ := n - 2 - k₂.val
    have hr_eq : r₁ = r₂ := by
      rcases lt_trichotomy r₁ r₂ with hlt | heq' | hgt
      · exfalso
        have h := hc0 r₁ (by have := k₁.isLt; omega)
        change PowerSeries.coeff r₁ (PowerSeries.X ^ r₁ * vOfBits gb₁) =
            PowerSeries.coeff r₁ (PowerSeries.X ^ r₂ * vOfBits gb₂) at h
        rw [PowerSeries.coeff_X_pow_mul', ite_eq_left le_rfl, tsub_self, coeff_zero_vOfBits,
          PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega : ¬ r₂ ≤ r₁)] at h
        exact one_ne_zero h
      · exact heq'
      · exfalso
        have h := hc0 r₂ (by have := k₂.isLt; omega)
        change PowerSeries.coeff r₂ (PowerSeries.X ^ r₁ * vOfBits gb₁) =
            PowerSeries.coeff r₂ (PowerSeries.X ^ r₂ * vOfBits gb₂) at h
        rw [PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega : ¬ r₁ ≤ r₂),
          PowerSeries.coeff_X_pow_mul', ite_eq_left le_rfl, tsub_self, coeff_zero_vOfBits] at h
        exact zero_ne_one h
    have hk_eq : k₁ = k₂ := by
      ext
      dsimp only [r₁, r₂] at hr_eq
      have := k₁.isLt
      have := k₂.isLt
      omega
    subst hk_eq
    have hgb : gb₁ = gb₂ := by
      funext j
      have hd : j.val + 1 + r₁ < n - 1 := by
        dsimp only [r₁]
        have := k₁.isLt
        have := j.isLt
        omega
      have h := hc0 (j.val + 1 + r₁) hd
      change PowerSeries.coeff (j.val + 1 + r₁) (PowerSeries.X ^ r₁ * vOfBits gb₁) =
          PowerSeries.coeff (j.val + 1 + r₁) (PowerSeries.X ^ r₁ * vOfBits gb₂) at h
      rw [PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_X_pow_mul,
        coeff_succ_vOfBits_of_lt, coeff_succ_vOfBits_of_lt] at h
      exact h
    subst hgb
    have hfb : fb₁ = fb₂ := by
      rcases Nat.eq_zero_or_pos k₁.val with hk0 | hkpos
      · funext j
        exact absurd j.isLt (by omega)
      · have hc1 := hcols 1 (by have := k₁.isLt; omega)
        simp only [evalCanonParam, pow_one] at hc1
        change EqMod (n - 1) (PowerSeries.X ^ r₁ * vOfBits gb₁ * fOfBits fb₁)
            (PowerSeries.X ^ r₁ * vOfBits gb₁ * fOfBits fb₂) at hc1
        have hsum := EqMod.add hc1 (EqMod.refl (n - 1)
          (PowerSeries.X ^ r₁ * vOfBits gb₁ * fOfBits fb₂))
        rw [ps_add_self, show PowerSeries.X ^ r₁ * vOfBits gb₁ * fOfBits fb₁ +
            PowerSeries.X ^ r₁ * vOfBits gb₁ * fOfBits fb₂ =
            PowerSeries.X ^ r₁ * (vOfBits gb₁ * (fOfBits fb₁ + fOfBits fb₂)) by ring] at hsum
        rw [EqMod.X_pow_mul_zero_iff,
          EqMod.cancel_unit_zero (coeff_zero_vOfBits gb₁)] at hsum
        funext j
        have hj : j.val + 1 < n - 1 - r₁ := by
          dsimp only [r₁]
          have := k₁.isLt
          have := j.isLt
          omega
        have h := hsum (j.val + 1) hj
        rw [map_add, coeff_succ_fOfBits_of_lt, coeff_succ_fOfBits_of_lt, map_zero,
          zmod2_add_eq_zero_iff] at h
        exact h
    subst hfb
    rfl

theorem graphOfCanonParam_surjective (n : ℕ) : Function.Surjective (graphOfCanonParam n) := by
  rintro ⟨G, hG⟩
  obtain ⟨g, f, hf0, rfl⟩ := (isLabeledRiordanGraph_iff_exists_eq n G).mp hG
  by_cases hzero : ∀ d < n - 1, PowerSeries.coeff d g = 0
  · refine ⟨Sum.inl (), Subtype.ext ?_⟩
    symm
    dsimp only [graphOfCanonParam, evalCanonParam]
    rw [riordanGraph_eq_iff hf0 (by simp)]
    intro c hc d hd
    have hg_mod : EqMod (n - 1) g 0 := fun i hi => by simpa using hzero i hi
    have hmul := EqMod.mul hg_mod (EqMod.refl (n - 1) (f ^ c))
    simpa using hmul d hd
  · classical
    have hex : ∃ d, d < n - 1 ∧ PowerSeries.coeff d g ≠ 0 := by
      by_contra hcon
      apply hzero
      intro d hd
      by_contra hne
      exact hcon ⟨d, hd, hne⟩
    obtain ⟨r, hr_find⟩ : ∃ r, r = Nat.find hex := ⟨Nat.find hex, rfl⟩
    have hr_spec : r < n - 1 ∧ PowerSeries.coeff r g ≠ 0 := hr_find ▸ Nat.find_spec hex
    have hr_lt : r < n - 1 := hr_spec.1
    have hr_min : ∀ d < r, PowerSeries.coeff d g = 0 := by
      intro d hd
      by_contra hne
      exact Nat.find_min hex (hr_find ▸ hd) ⟨lt_trans hd hr_lt, hne⟩
    have hrg : PowerSeries.coeff r g = 1 := (zmod2_ne_zero_iff_eq_one _).mp hr_spec.2
    let k : Fin (n - 1) := ⟨n - 2 - r, by omega⟩
    have hk_val : k.val = n - 2 - r := rfl
    have hr_eq : n - 2 - k.val = r := by rw [hk_val]; omega
    let gb : Fin k.val → ZMod 2 := fun j => PowerSeries.coeff (r + (j.val + 1)) g
    let fb : Fin k.val → ZMod 2 := fun j => PowerSeries.coeff (j.val + 1) f
    refine ⟨Sum.inr ⟨k, (gb, fb)⟩, Subtype.ext ?_⟩
    symm
    dsimp only [graphOfCanonParam, evalCanonParam]
    rw [hr_eq, riordanGraph_eq_iff hf0 (coeff_zero_fOfBits fb)]
    have hg_mod : EqMod (n - 1) g (PowerSeries.X ^ r * vOfBits gb) := by
      intro d hd
      rw [PowerSeries.coeff_X_pow_mul']
      split_ifs with hrd
      · rcases eq_or_lt_of_le hrd with rfl | hrlt
        · simp [hrg]
        · have hjlt : d - r - 1 < k.val := by rw [hk_val]; omega
          have hsub : d - r = (d - r - 1) + 1 := by omega
          rw [hsub, coeff_succ_vOfBits_of_lt gb ⟨d - r - 1, hjlt⟩]
          have hidx : r + (d - r - 1 + 1) = d := by omega
          simp only [gb, hidx]
      · exact hr_min d (by omega)
    have hf_mod : EqMod (k.val + 1) f (fOfBits fb) := by
      intro d hd
      rcases d with _ | d
      · simp [hf0]
      · have hjlt : d < k.val := by omega
        rw [coeff_succ_fOfBits_of_lt fb ⟨d, hjlt⟩]
    intro c _hc
    rcases c with _ | c
    · simpa using hg_mod
    · have hfc : EqMod (k.val + 1) (f ^ (c + 1)) ((fOfBits fb) ^ (c + 1)) :=
        EqMod.pow hf_mod (c + 1)
      have hvd : EqMod (k.val + 1)
          (vOfBits gb * (f ^ (c + 1) + (fOfBits fb) ^ (c + 1))) 0 := by
        have h := EqMod.mul (EqMod.refl (k.val + 1) (vOfBits gb))
          (EqMod.add hfc (EqMod.refl (k.val + 1) ((fOfBits fb) ^ (c + 1))))
        rwa [ps_add_self, mul_zero] at h
      have hkm : k.val + 1 = n - 1 - r := by omega
      rw [hkm, ← EqMod.X_pow_mul_zero_iff] at hvd
      have hstep2 : EqMod (n - 1)
          (PowerSeries.X ^ r * vOfBits gb * f ^ (c + 1))
          (PowerSeries.X ^ r * vOfBits gb * (fOfBits fb) ^ (c + 1)) := by
        have h := EqMod.add hvd (EqMod.refl (n - 1)
          (PowerSeries.X ^ r * vOfBits gb * (fOfBits fb) ^ (c + 1)))
        rwa [zero_add, show PowerSeries.X ^ r * (vOfBits gb * (f ^ (c + 1) + (fOfBits fb) ^ (c + 1))) +
            PowerSeries.X ^ r * vOfBits gb * (fOfBits fb) ^ (c + 1) =
            PowerSeries.X ^ r * vOfBits gb * f ^ (c + 1) +
              (PowerSeries.X ^ r * vOfBits gb * (fOfBits fb) ^ (c + 1) +
                PowerSeries.X ^ r * vOfBits gb * (fOfBits fb) ^ (c + 1)) by ring,
          ps_add_self, add_zero] at h
      exact (EqMod.mul hg_mod (EqMod.refl (n - 1) (f ^ (c + 1)))).trans hstep2

/-- Step 2 bijection: `CanonParam n` bijects onto all labeled Riordan graphs on `Fin n`. -/
noncomputable def canonParamEquiv (n : ℕ) :
    CanonParam n ≃ { G : SimpleGraph (Fin n) // IsLabeledRiordanGraph n G } :=
  Equiv.ofBijective (graphOfCanonParam n)
    ⟨graphOfCanonParam_injective n, graphOfCanonParam_surjective n⟩

/-- Total number of labeled Riordan graphs of order `n` (`OEIS A047849(n - 1)` for `n ≥ 1`). -/
noncomputable def labeledRiordanCount (n : ℕ) : ℕ :=
  Nat.card { G : SimpleGraph (Fin n) // IsLabeledRiordanGraph n G }

/-- Sanity check against `OEIS A047849(n - 1)`: `L(n) = 1 + ∑_{k=0}^{n-2} 4^k` satisfies
`3 * L(n) = 4^(n - 1) + 2`. -/
theorem three_mul_labeledRiordanCount_eq (n : ℕ) :
    3 * labeledRiordanCount n = 4 ^ (n - 1) + 2 := by
  have hcard : labeledRiordanCount n = 1 + ∑ k ∈ Finset.range (n - 1), 4 ^ k := by
    rw [labeledRiordanCount, ← Nat.card_congr (canonParamEquiv n), Nat.card_eq_fintype_card,
      Fintype.card_sum, Fintype.card_unit, Fintype.card_sigma, Finset.sum_range]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card 2, ← pow_add, ← two_mul,
      pow_mul]
    norm_num
  rw [hcard]
  have hgeom : ∀ m : ℕ, 3 * (1 + ∑ k ∈ Finset.range m, 4 ^ k) = 4 ^ m + 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, pow_succ]
      omega
  exact hgeom (n - 1)

/-! ### Step 5 (`SCOPING-S012.md` §2.1): Exact Layer Count & Closed Telescopic Recurrence -/

/-- Layer `k` Frobenius squaring constraint: `(fOfBits fb + X)^2 ≡ 0 (mod X^(k + 1))` iff the
first `⌊k / 2⌋` bits of `fb` match `(1, 0, 0, …)` and the remaining `k - ⌊k / 2⌋` bits are free. -/
theorem fOfBits_add_X_sq_eqMod_zero_iff (k : ℕ) (fb : Fin k → ZMod 2) :
    EqMod (k + 1) ((fOfBits fb + PowerSeries.X) ^ 2) 0 ↔
      ∀ j : Fin k, j.val < k / 2 → fb j = (if j.val = 0 then 1 else 0) := by
  constructor
  · intro h j hj
    have hd : 2 * (j.val + 1) < k + 1 := by omega
    have hcoeff := h (2 * (j.val + 1)) hd
    rw [coeff_sq_zmod2, ite_eq_left (by omega : 2 * (j.val + 1) % 2 = 0),
      show 2 * (j.val + 1) / 2 = j.val + 1 by omega, map_add,
      coeff_succ_fOfBits_of_lt fb j, PowerSeries.coeff_X, map_zero,
      zmod2_add_eq_zero_iff] at hcoeff
    simpa [Nat.add_eq_right] using hcoeff
  · intro h e he
    rw [coeff_sq_zmod2, map_zero]
    split_ifs with heven
    · rcases Nat.eq_zero_or_pos e with rfl | hepos
      · simp
      · have hd1 : 1 ≤ e / 2 := by omega
        have hjlt : e / 2 - 1 < k / 2 := by omega
        have hjlt_k : e / 2 - 1 < k := by omega
        let j : Fin k := ⟨e / 2 - 1, hjlt_k⟩
        have hsub : e / 2 = j.val + 1 := by simp [j]; omega
        rw [hsub, map_add, coeff_succ_fOfBits_of_lt fb j, PowerSeries.coeff_X, h j hjlt]
        have hcond : (j.val + 1 = 1) ↔ (j.val = 0) := by omega
        simp only [hcond]
        exact zmod2_add_self _
    · rfl

/-- Explicit bijection between constrained `f`-bitvectors in layer `k` and unconstrained
free bitvectors `Fin (k - k / 2) → ZMod 2`. -/
def validFBitsEquiv (k : ℕ) :
    (Fin (k - k / 2) → ZMod 2) ≃
      { fb : Fin k → ZMod 2 // ∀ j : Fin k, j.val < k / 2 → fb j = if j.val = 0 then 1 else 0 } where
  toFun free :=
    ⟨fun j =>
        if h : j.val < k / 2 then (if j.val = 0 then 1 else 0)
        else free ⟨j.val - k / 2, by omega⟩,
      fun j hj => by simp [hj]⟩
  invFun fb i := fb.1 ⟨i.val + k / 2, by omega⟩
  left_inv free := by
    funext i
    have hnot : ¬ (i.val + k / 2 < k / 2) := by omega
    simp [hnot]
  right_inv := by
    rintro ⟨fb, hfb⟩
    ext j
    by_cases hj : j.val < k / 2
    · simp [hj, hfb j hj]
    · simp only [hj, dite_false]
      exact congrArg fb (Fin.ext (by dsimp; omega))

/-- Finite parameter space for complement-closed labeled Riordan graphs on `g₀ = 0` (`n ≥ 2`):
`Unit` (`(0, 0)`) plus layers `k : Fin (n - 2)` with `2^k * 2^(k - k/2)` free bits. -/
abbrev ValidZeroParam (n : ℕ) : Type :=
  Unit ⊕ Σ k : Fin (n - 2), (Fin k.val → ZMod 2) × (Fin (k.val - k.val / 2) → ZMod 2)

noncomputable def validZeroToCanon {n : ℕ} (hn : 2 ≤ n) : ValidZeroParam n → CanonParam n
  | Sum.inl () => Sum.inl ()
  | Sum.inr ⟨k, (gb, free)⟩ =>
      Sum.inr ⟨⟨k.val, by omega⟩, (gb, (validFBitsEquiv k.val free).1)⟩

theorem validZeroToCanon_injective {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective (validZeroToCanon hn) := by
  rintro (⟨⟩ | ⟨k₁, gb₁, free₁⟩) (⟨⟩ | ⟨k₂, gb₂, free₂⟩) heq
  · rfl
  · cases heq
  · cases heq
  · simp only [validZeroToCanon, Sum.inr.injEq, Sigma.mk.inj_iff, Fin.mk.injEq] at heq
    obtain ⟨hk, hrest⟩ := heq
    have hk_ext : k₁ = k₂ := Fin.ext hk
    subst hk_ext
    simp only [heq_eq_eq, Prod.mk.injEq] at hrest
    obtain ⟨rfl, hfb⟩ := hrest
    have hfree : free₁ = free₂ := (validFBitsEquiv k₁.val).injective (Subtype.ext hfb)
    subst hfree
    rfl

theorem canonParam_in_ccSetZero_iff {n : ℕ} (hn : 2 ≤ n) (p : CanonParam n) :
    (¬ (graphOfCanonParam n p).1.Adj ⟨1, by omega⟩ ⟨0, by omega⟩ ∧
        IsLabeledRiordanGraph n (graphOfCanonParam n p).1ᶜ) ↔
      ∃ q : ValidZeroParam n, validZeroToCanon hn q = p := by
  rcases p with ⟨⟩ | ⟨k, gb, fb⟩
  · constructor
    · intro _
      exact ⟨Sum.inl (), rfl⟩
    · intro _
      have hg0 : PowerSeries.coeff 0 (0 : PS) = 0 := by simp
      have hf0 : PowerSeries.coeff 0 (0 : PS) = 0 := by simp
      dsimp only [graphOfCanonParam, evalCanonParam]
      refine ⟨(riordanGraph_not_adj_one_zero_iff hn 0 0).mpr hg0, ?_⟩
      rw [master_characterization_on_g0_zero hf0 hg0]
      simpa using EqMod.refl (n - 1) 0
  · let r := n - 2 - k.val
    let g := PowerSeries.X ^ r * vOfBits gb
    let f := fOfBits fb
    have hf0 : PowerSeries.coeff 0 f = 0 := coeff_zero_fOfBits fb
    have hg0_iff : PowerSeries.coeff 0 g = 0 ↔ k.val < n - 2 := by
      simp only [g, r, PowerSeries.coeff_X_pow_mul']
      have hklt := k.isLt
      split_ifs with hr0
      · constructor
        · intro h
          simp at h
        · intro hlt
          omega
      · exact ⟨fun _ => by omega, fun _ => rfl⟩
    constructor
    · rintro ⟨hnotAdj, hcompl⟩
      dsimp only [graphOfCanonParam, evalCanonParam] at hnotAdj hcompl
      have hg0 : PowerSeries.coeff 0 g = 0 :=
        (riordanGraph_not_adj_one_zero_iff hn g f).mp hnotAdj
      have hk2 : k.val < n - 2 := hg0_iff.mp hg0
      change IsLabeledRiordanGraph n (riordanGraph n g f)ᶜ at hcompl
      rw [master_characterization_on_g0_zero hf0 hg0] at hcompl
      have hstrip : EqMod (k.val + 1) ((f + PowerSeries.X) ^ 2) 0 := by
        rw [show g * (f + PowerSeries.X) ^ 2 =
            PowerSeries.X ^ r * (vOfBits gb * (f + PowerSeries.X) ^ 2) by ring,
          EqMod.X_pow_mul_zero_iff,
          show n - 1 - r = k.val + 1 by simp [r]; omega,
          EqMod.cancel_unit_zero (coeff_zero_vOfBits gb)] at hcompl
        exact hcompl
      have hfb := (fOfBits_add_X_sq_eqMod_zero_iff k.val fb).mp hstrip
      refine ⟨Sum.inr ⟨⟨k.val, hk2⟩, (gb, (validFBitsEquiv k.val).symm ⟨fb, hfb⟩)⟩, ?_⟩
      simp only [validZeroToCanon, Equiv.apply_symm_apply, Fin.eta]
    · rintro ⟨q, hq⟩
      rcases q with ⟨⟩ | ⟨k', gb', free⟩
      · cases hq
      · simp only [validZeroToCanon, Sum.inr.injEq] at hq
        have hk_val : k'.val = k.val := by
          have := congr_arg Sigma.fst hq
          simpa using congr_arg Fin.val this
        have hk2 : k.val < n - 2 := hk_val ▸ k'.isLt
        have hk'_eq : k' = ⟨k.val, hk2⟩ := Fin.ext hk_val
        subst hk'_eq
        simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] at hq
        obtain ⟨_, rfl, rfl⟩ := hq
        have hg0 : PowerSeries.coeff 0 g = 0 := hg0_iff.mpr hk2
        dsimp only [graphOfCanonParam, evalCanonParam]
        refine ⟨(riordanGraph_not_adj_one_zero_iff hn g _).mpr hg0, ?_⟩
        change IsLabeledRiordanGraph n
          (riordanGraph n g (fOfBits (validFBitsEquiv k.val free).1))ᶜ
        rw [master_characterization_on_g0_zero (coeff_zero_fOfBits _) hg0,
          show g * (fOfBits (validFBitsEquiv k.val free).1 + PowerSeries.X) ^ 2 =
            PowerSeries.X ^ r * (vOfBits gb' *
              (fOfBits (validFBitsEquiv k.val free).1 + PowerSeries.X) ^ 2) by ring,
          EqMod.X_pow_mul_zero_iff,
          show n - 1 - r = k.val + 1 by simp [r]; omega,
          EqMod.cancel_unit_zero (coeff_zero_vOfBits gb'),
          fOfBits_add_X_sq_eqMod_zero_iff]
        exact (validFBitsEquiv k.val free).2

/-- Bijection between `ValidZeroParam n` and `CCSetZero n hn` (`n ≥ 2`). -/
noncomputable def validZeroParamEquiv {n : ℕ} (hn : 2 ≤ n) :
    ValidZeroParam n ≃ CCSetZero n hn := by
  refine Equiv.ofBijective
    (fun q =>
      let p := validZeroToCanon hn q
      have hp := (canonParam_in_ccSetZero_iff hn p).mpr ⟨q, rfl⟩
      ⟨(graphOfCanonParam n p).1, hp.1, (graphOfCanonParam n p).2, hp.2⟩)
    ⟨?_, ?_⟩
  · intro q₁ q₂ heq
    have hG : graphOfCanonParam n (validZeroToCanon hn q₁) =
        graphOfCanonParam n (validZeroToCanon hn q₂) :=
      Subtype.ext (Subtype.mk.inj heq)
    exact validZeroToCanon_injective hn (graphOfCanonParam_injective n hG)
  · rintro ⟨G, hnotAdj, hG, hGc⟩
    obtain ⟨p, hp⟩ := graphOfCanonParam_surjective n ⟨G, hG⟩
    have hpG : (graphOfCanonParam n p).1 = G := congr_arg Subtype.val hp
    obtain ⟨q, rfl⟩ := (canonParam_in_ccSetZero_iff hn p).mp ⟨hpG ▸ hnotAdj, hpG ▸ hGc⟩
    refine ⟨q, Subtype.ext hpG⟩

/-- Exact closed-layer count (`SCOPING-S012.md` §2.1 Step 5):
for every `n ≥ 2`, `a(n) = 2 * (1 + ∑_{k=0}^{n-3} 2^(2k - ⌊k/2⌋))`. -/
theorem count_eq_closed_layer_sum {n : ℕ} (hn : 2 ≤ n) :
    complementClosedRiordanCount n =
      2 * (1 + ∑ k ∈ Finset.range (n - 2), 2 ^ (2 * k - k / 2)) := by
  have hequiv : ValidZeroParam n ⊕ ValidZeroParam n ≃ CCSet n :=
    (Equiv.sumCongr (validZeroParamEquiv hn) (validZeroParamEquiv hn)).trans (complDoubleEquiv hn)
  rw [complementClosedRiordanCount, ← Nat.card_congr hequiv, Nat.card_eq_fintype_card,
    Fintype.card_sum, ← two_mul, Fintype.card_sum, Fintype.card_unit, Fintype.card_sigma,
    Finset.sum_range]
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    ZMod.card 2, ← pow_add]
  congr 1
  omega

/-! ### Pinned Target Theorems (`PIN-S012.md` v1) -/

/-- Base value at `n = 1` (`OEIS A401496` `%O 1,2`, `%S` line 7 first entry). -/
theorem complementClosed_riordan_count_one : complementClosedRiordanCount 1 = 1 := by
  have hb : IsLabeledRiordanGraph 1 (⊥ : SimpleGraph (Fin 1)) :=
    ⟨0, 0, by simp, fun i j hij => absurd hij (by omega)⟩
  have hbot_compl : (⊥ : SimpleGraph (Fin 1))ᶜ = ⊥ := by
    ext u v
    have huv : u = v := Fin.ext (by omega)
    subst huv
    simp
  have hb_compl : IsLabeledRiordanGraph 1 (⊥ : SimpleGraph (Fin 1))ᶜ := by
    rw [hbot_compl]
    exact hb
  have hne : Nonempty (CCSet 1) := ⟨⟨⊥, hb, hb_compl⟩⟩
  have hsub : Subsingleton (CCSet 1) :=
    ⟨fun ⟨G, _, _⟩ ⟨H, _, _⟩ => by
      ext u v
      have huv : u = v := Fin.ext (by omega)
      subst huv
      simp⟩
  exact @Nat.card_unique (CCSet 1) hne hsub

/-- Base value at `n = 2` (`OEIS A401496` `%O 1,2`, `%S` line 7 second entry). -/
theorem complementClosed_riordan_count_two : complementClosedRiordanCount 2 = 2 := by
  rw [count_eq_closed_layer_sum (by omega : 2 ≤ 2)]
  simp

/-- Main recurrence (`OEIS A401496` `%F` line 12, Arnauld Mesinga Mwafise, Oct 27 2026):
for every `n : ℕ` with `3 ≤ n`, `a(n) = 8 * a(n - 2) - 4`. -/
theorem complementClosed_riordan_count_eq (n : ℕ) (hn : 3 ≤ n) :
    complementClosedRiordanCount n = 8 * complementClosedRiordanCount (n - 2) - 4 := by
  rcases eq_or_lt_of_le hn with rfl | hn4
  · rw [count_eq_closed_layer_sum (by omega : 2 ≤ 3),
      show (3 : ℕ) - 2 = 1 from rfl, complementClosed_riordan_count_one]
    simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [count_eq_closed_layer_sum (by omega : 2 ≤ m + 4),
      show m + 4 - 2 = m + 2 by omega,
      count_eq_closed_layer_sum (by omega : 2 ≤ m + 2),
      show m + 2 - 2 = m by omega]
    let f : ℕ → ℕ := fun k => 2 ^ (2 * k - k / 2)
    have hpeel1 : ∑ k ∈ Finset.range (m + 2), f k =
        (∑ k ∈ Finset.range (m + 1), f (k + 1)) + f 0 :=
      Finset.sum_range_succ' f (m + 1)
    have hpeel2 : ∑ k ∈ Finset.range (m + 1), f (k + 1) =
        (∑ k ∈ Finset.range m, f (k + 2)) + f 1 :=
      Finset.sum_range_succ' (fun k => f (k + 1)) m
    have hshift : ∑ k ∈ Finset.range m, f (k + 2) = 8 * ∑ k ∈ Finset.range m, f k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [f]
      have hexp : 2 * (k + 2) - (k + 2) / 2 = 3 + (2 * k - k / 2) := by omega
      rw [hexp, pow_add]
      norm_num
    have hf0 : f 0 = 1 := by simp [f]
    have hf1 : f 1 = 4 := by simp [f]
    change 2 * (1 + ∑ k ∈ Finset.range (m + 2), f k) =
      8 * (2 * (1 + ∑ k ∈ Finset.range m, f k)) - 4
    rw [hpeel1, hpeel2, hshift, hf0, hf1]
    omega

/-! ### Section 6: Computable Mirrors, OEIS `n = 1..14` Spot Checks, & Boundary Non-Vacuity -/

/-- `n = 0` value (`complementClosedRiordanCount 0 = 1`, outside OEIS `%O 1,2` domain). -/
theorem complementClosed_riordan_count_zero : complementClosedRiordanCount 0 = 1 := by
  have hb : IsLabeledRiordanGraph 0 (⊥ : SimpleGraph (Fin 0)) :=
    ⟨0, 0, by simp, fun i _ _ => Fin.elim0 i⟩
  have hbot_compl : (⊥ : SimpleGraph (Fin 0))ᶜ = ⊥ := by
    ext u
    exact Fin.elim0 u
  have hb_compl : IsLabeledRiordanGraph 0 (⊥ : SimpleGraph (Fin 0))ᶜ := by
    rw [hbot_compl]
    exact hb
  have hne : Nonempty (CCSet 0) := ⟨⟨⊥, hb, hb_compl⟩⟩
  have hsub : Subsingleton (CCSet 0) :=
    ⟨fun ⟨G, _, _⟩ ⟨H, _, _⟩ => by
      ext u
      exact Fin.elim0 u⟩
  exact @Nat.card_unique (CCSet 0) hne hsub

/-- Pure `Nat`-recursion mirror of `∑_{k=0}^{m-1} 2^(2k - ⌊k/2⌋)`, free of `Finset`/`Quot` terms. -/
def layerSumFast : ℕ → ℕ
  | 0 => 0
  | k + 1 => layerSumFast k + 2 ^ (2 * k - k / 2)

/-- Pure `Nat`-recursion mirror of `complementClosedRiordanCount n` for all `n : ℕ`. -/
def complementClosedLayerFast : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | m + 2 => 2 * (1 + layerSumFast m)

private theorem layerSumFast_eq_sum (m : ℕ) :
    layerSumFast m = ∑ k ∈ Finset.range m, 2 ^ (2 * k - k / 2) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [layerSumFast, ih, Finset.sum_range_succ]

theorem complementClosedLayerFast_eq (n : ℕ) :
    complementClosedLayerFast n = complementClosedRiordanCount n := by
  match n with
  | 0 => exact complementClosed_riordan_count_zero.symm
  | 1 => exact complementClosed_riordan_count_one.symm
  | m + 2 =>
    rw [complementClosedLayerFast, layerSumFast_eq_sum,
      count_eq_closed_layer_sum (by omega : 2 ≤ m + 2)]
    rfl

/-- Direct finite-jet Cauchy product on `Fin m → ZMod 2` (used for the Step-2..5-independent
computable brute-force mirror `complementClosedRiordanCountJet`). -/
def jetMul {m : ℕ} (a b : Fin m → ZMod 2) : Fin m → ZMod 2 :=
  fun d => ∑ i : Fin (d.val + 1), a ⟨i.val, by omega⟩ * b ⟨d.val - i.val, by omega⟩

def jetOne (m : ℕ) : Fin m → ZMod 2 :=
  fun d => if d.val = 0 then 1 else 0

def jetPow {m : ℕ} (a : Fin m → ZMod 2) : ℕ → (Fin m → ZMod 2)
  | 0 => jetOne m
  | c + 1 => jetMul (jetPow a c) a

noncomputable def jetOfPS (m : ℕ) (p : PS) : Fin m → ZMod 2 :=
  fun d => PowerSeries.coeff d.val p

noncomputable def psOfJet {m : ℕ} (a : Fin m → ZMod 2) : PS :=
  PowerSeries.mk fun d => if h : d < m then a ⟨d, h⟩ else 0

private theorem jetOfPS_psOfJet {m : ℕ} (a : Fin m → ZMod 2) :
    jetOfPS m (psOfJet a) = a := by
  funext d
  simp [jetOfPS, psOfJet, d.isLt]

private theorem jetOfPS_mul {m : ℕ} (p q : PS) :
    jetOfPS m (p * q) = jetMul (jetOfPS m p) (jetOfPS m q) := by
  funext d
  simp only [jetOfPS, jetMul, PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y => PowerSeries.coeff x p * PowerSeries.coeff y q) d.val, Finset.sum_range]

private theorem jetOfPS_pow {m : ℕ} (p : PS) :
    ∀ c : ℕ, jetOfPS m (p ^ c) = jetPow (jetOfPS m p) c
  | 0 => by
    funext d
    simp [jetOfPS, jetPow, jetOne, PowerSeries.coeff_one]
  | c + 1 => by
    rw [pow_succ, jetPow, jetOfPS_mul, jetOfPS_pow p c]

/-- Strictly lower-triangular index pairs `(i, j)` with `j < i < n` (`n(n-1)/2` edge slots). -/
abbrev LowerTri (n : ℕ) : Type :=
  Σ i : Fin n, Fin i.val

def graphOfLowerTri {n : ℕ} (M : LowerTri n → Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => ∃ h : j.val < i.val, M ⟨i, ⟨j.val, h⟩⟩ = true

private theorem graphOfLowerTri_adj {n : ℕ} (M : LowerTri n → Bool) {i j : Fin n}
    (hij : j.val < i.val) :
    (graphOfLowerTri M).Adj i j ↔ M ⟨i, ⟨j.val, hij⟩⟩ = true := by
  rw [graphOfLowerTri, SimpleGraph.fromRel_adj]
  have hne : i ≠ j := fun h => by rw [h] at hij; exact Nat.lt_irrefl _ hij
  constructor
  · rintro ⟨_, ⟨h, hM⟩ | ⟨h, _⟩⟩
    · exact hM
    · exact absurd h (by omega)
  · intro hM
    exact ⟨hne, Or.inl ⟨hij, hM⟩⟩

private theorem graphOfLowerTri_not {n : ℕ} (M : LowerTri n → Bool) :
    graphOfLowerTri (fun e => !M e) = (graphOfLowerTri M)ᶜ := by
  ext u v
  rcases lt_trichotomy v.val u.val with hlt | heq | hgt
  · have hne : u ≠ v := fun h => by rw [h] at hlt; exact Nat.lt_irrefl _ hlt
    rw [graphOfLowerTri_adj _ hlt, SimpleGraph.compl_adj, and_iff_right hne,
      graphOfLowerTri_adj _ hlt, Bool.not_eq_true']
    simp
  · have huv : u = v := Fin.ext heq.symm
    subst huv
    simp
  · have hne : u ≠ v := fun h => by rw [h] at hgt; exact Nat.lt_irrefl _ hgt
    rw [(graphOfLowerTri _).adj_comm, graphOfLowerTri_adj _ hgt, SimpleGraph.compl_adj,
      and_iff_right hne, (graphOfLowerTri M).adj_comm, graphOfLowerTri_adj _ hgt,
      Bool.not_eq_true']
    simp

def fJetOfShort {n : ℕ} (f : Fin (n - 2) → ZMod 2) : Fin (n - 1) → ZMod 2 :=
  fun d =>
    if d.val = 0 then 0
    else if h : d.val - 1 < n - 2 then f ⟨d.val - 1, h⟩
    else 0

/-- Decidable finite-jet Riordan predicate on strictly lower-triangular boolean matrices. -/
def IsRiordanLowerTri (n : ℕ) (M : LowerTri n → Bool) : Prop :=
  ∃ (g : Fin (n - 1) → ZMod 2) (f : Fin (n - 2) → ZMod 2),
    ∀ e : LowerTri n,
      (M e = true ↔
        jetMul g (jetPow (fJetOfShort f) e.2.val)
          ⟨e.1.val - 1, by have := e.2.isLt; have := e.1.isLt; omega⟩ = 1)

instance instDecidablePredIsRiordanLowerTri (n : ℕ) : DecidablePred (IsRiordanLowerTri n) := by
  intro M
  unfold IsRiordanLowerTri
  infer_instance

/-- Direct brute-force computable mirror enumerating all `2^(n(n-1)/2)` labeled graphs on `Fin n`
and testing both `G` and `Gᶜ` against `(n - 1)`-jets over `ZMod 2`. -/
def complementClosedRiordanCountJet (n : ℕ) : ℕ :=
  Fintype.card { M : LowerTri n → Bool //
    IsRiordanLowerTri n M ∧ IsRiordanLowerTri n (fun e => !M e) }

private theorem isRiordanLowerTri_iff (n : ℕ) (M : LowerTri n → Bool) :
    IsRiordanLowerTri n M ↔ IsLabeledRiordanGraph n (graphOfLowerTri M) := by
  constructor
  · rintro ⟨g, f, hspec⟩
    refine ⟨psOfJet g, psOfJet (fJetOfShort f), ?_, ?_⟩
    · simp [psOfJet, fJetOfShort]
    · intro i j hij
      rw [graphOfLowerTri_adj M hij, hspec ⟨i, ⟨j.val, hij⟩⟩]
      have hd : i.val - 1 < n - 1 := by omega
      have hjet := congr_fun (jetOfPS_mul (m := n - 1) (psOfJet g)
        ((psOfJet (fJetOfShort f)) ^ j.val)) ⟨i.val - 1, hd⟩
      rw [jetOfPS_psOfJet, jetOfPS_pow, jetOfPS_psOfJet] at hjet
      simp only [jetOfPS] at hjet
      rw [← hjet]
  · rintro ⟨g, f, hf0, hspec⟩
    let gJ : Fin (n - 1) → ZMod 2 := jetOfPS (n - 1) g
    let fS : Fin (n - 2) → ZMod 2 := fun j => PowerSeries.coeff (j.val + 1) f
    have hfJ_eq : fJetOfShort fS = jetOfPS (n - 1) f := by
      funext d
      rcases Nat.eq_zero_or_pos d.val with hd0 | hdpos
      · simp [fJetOfShort, jetOfPS, hd0, hf0]
      · have hlt : d.val - 1 < n - 2 := by have := d.isLt; omega
        have hsub : d.val - 1 + 1 = d.val := by omega
        simp [fJetOfShort, jetOfPS, fS, Nat.ne_of_gt hdpos, hlt, hsub]
    refine ⟨gJ, fS, fun e => ?_⟩
    let jFin : Fin n := ⟨e.2.val, lt_trans e.2.isLt e.1.isLt⟩
    have hij : jFin.val < e.1.val := e.2.isLt
    have he_eq : (⟨e.1, ⟨jFin.val, hij⟩⟩ : LowerTri n) = e := rfl
    rw [← he_eq, ← graphOfLowerTri_adj M hij, hspec e.1 jFin hij, hfJ_eq]
    have hjet := congr_fun (jetOfPS_mul (m := n - 1) g (f ^ jFin.val))
      ⟨e.1.val - 1, by have := e.1.isLt; omega⟩
    rw [jetOfPS_pow] at hjet
    simp only [jetOfPS, gJ] at hjet ⊢
    rw [hjet]

/-- Equivalence between `complementClosedRiordanCountJet` and the pinned
`complementClosedRiordanCount`, proved directly from jet truncation and `LowerTri` without using
Steps 2–5 (`CanonParam`, `master_characterization_on_g0_zero`, or `count_eq_closed_layer_sum`). -/
theorem complementClosedRiordanCountJet_eq (n : ℕ) :
    complementClosedRiordanCountJet n = complementClosedRiordanCount n := by
  classical
  let hgraphEquiv : (LowerTri n → Bool) ≃ SimpleGraph (Fin n) :=
    { toFun := graphOfLowerTri
      invFun := fun G e => decide (G.Adj e.1 ⟨e.2.val, lt_trans e.2.isLt e.1.isLt⟩)
      left_inv := fun M => by
        funext e
        dsimp only
        rw [graphOfLowerTri_adj M e.2.isLt]
        simp
      right_inv := fun G => by
        ext u v
        rcases lt_trichotomy v.val u.val with hlt | heq | hgt
        · rw [graphOfLowerTri_adj _ hlt]
          simp
        · have huv : u = v := Fin.ext heq.symm
          subst huv
          simp
        · rw [(graphOfLowerTri _).adj_comm, G.adj_comm, graphOfLowerTri_adj _ hgt]
          simp }
  let subEquiv :
      { M : LowerTri n → Bool // IsRiordanLowerTri n M ∧ IsRiordanLowerTri n (fun e => !M e) } ≃
        CCSet n :=
    { toFun := fun ⟨M, hM, hMc⟩ =>
        ⟨graphOfLowerTri M, (isRiordanLowerTri_iff n M).mp hM,
          graphOfLowerTri_not M ▸ (isRiordanLowerTri_iff n _).mp hMc⟩
      invFun := fun ⟨G, hG, hGc⟩ =>
        let M := hgraphEquiv.symm G
        have hMG : graphOfLowerTri M = G := hgraphEquiv.apply_symm_apply G
        ⟨M, (isRiordanLowerTri_iff n M).mpr (hMG ▸ hG),
          (isRiordanLowerTri_iff n _).mpr (by rw [graphOfLowerTri_not, hMG]; exact hGc)⟩
      left_inv := fun ⟨M, _, _⟩ => Subtype.ext (hgraphEquiv.symm_apply_apply M)
      right_inv := fun ⟨G, _, _⟩ => Subtype.ext (hgraphEquiv.apply_symm_apply G) }
  rw [complementClosedRiordanCount, ← Nat.card_congr subEquiv, Nat.card_eq_fintype_card,
    complementClosedRiordanCountJet]

/-- Kernel-verified spot checks of `complementClosedRiordanCount n` across all 14 printed terms
of live `OEIS A401496` (`%S` line 7, `n = 1..14`) and `labeledRiordanCount n` across `n = 1..10`
(`OEIS A047849(n - 1)`), with `0` `native_decide` and `0` `ofReduceBool`. -/
theorem complementClosed_spot_checks_1_to_14 :
    (List.range' 1 14).map complementClosedRiordanCount =
      [1, 2, 4, 12, 28, 92, 220, 732, 1756, 5852, 14044, 46812, 112348, 374492] ∧
    (List.range' 1 10).map labeledRiordanCount =
      [1, 2, 6, 22, 86, 342, 1366, 5462, 21846, 87382] := by
  have hfun : complementClosedRiordanCount = complementClosedLayerFast :=
    funext fun n => (complementClosedLayerFast_eq n).symm
  have hlfun : labeledRiordanCount = fun n => (4 ^ (n - 1) + 2) / 3 := by
    funext n
    have h3 := three_mul_labeledRiordanCount_eq n
    omega
  rw [hfun, hlfun]
  exact ⟨rfl, rfl⟩

/-- `a(1) = 1` is the unique odd value of `complementClosedRiordanCount n` for `n ≥ 1`. -/
theorem even_complementClosedRiordanCount {n : ℕ} (hn : 2 ≤ n) :
    Even (complementClosedRiordanCount n) := by
  rw [count_eq_closed_layer_sum hn]
  exact ⟨1 + ∑ k ∈ Finset.range (n - 2), 2 ^ (2 * k - k / 2), by ring⟩

theorem odd_complementClosedRiordanCount_iff {n : ℕ} (hn : 1 ≤ n) :
    Odd (complementClosedRiordanCount n) ↔ n = 1 := by
  rcases eq_or_lt_of_le hn with rfl | hn2
  · rw [complementClosed_riordan_count_one]
    exact ⟨fun _ => rfl, fun _ => ⟨0, rfl⟩⟩
  · constructor
    · intro hodd
      exact absurd hodd (Nat.not_odd_iff_even.mpr (even_complementClosedRiordanCount hn2))
    · intro h1
      omega

/-- Boundary check at `n = 2`: `(⊥ : SimpleGraph (Fin 2)) ≠ ⊤` and both graphs on `Fin 2` are
complement-closed labeled Riordan graphs (`G₂(0, 0) = ⊥` and `G₂(1, 0) = ⊤`). -/
theorem fin2_both_graphs_complementClosed :
    (⊥ : SimpleGraph (Fin 2)) ≠ ⊤ ∧
    (IsLabeledRiordanGraph 2 (⊥ : SimpleGraph (Fin 2)) ∧
      IsLabeledRiordanGraph 2 (⊥ : SimpleGraph (Fin 2))ᶜ) ∧
    (IsLabeledRiordanGraph 2 (⊤ : SimpleGraph (Fin 2)) ∧
      IsLabeledRiordanGraph 2 (⊤ : SimpleGraph (Fin 2))ᶜ) := by
  have hne : (⊥ : SimpleGraph (Fin 2)) ≠ ⊤ := by
    intro h
    have hadj : (⊤ : SimpleGraph (Fin 2)).Adj ⟨1, by omega⟩ ⟨0, by omega⟩ := by simp
    rw [← h] at hadj
    exact hadj
  have hbot : riordanGraph 2 0 0 = ⊥ := by
    symm
    apply eq_riordanGraph_of_spec
    intro i j hij
    have hi : i.val = 1 := by omega
    have hj : j.val = 0 := by omega
    simp [hi, hj]
  have htop : riordanGraph 2 1 0 = ⊤ := by
    symm
    apply eq_riordanGraph_of_spec
    intro i j hij
    have hi : i.val = 1 := by omega
    have hj : j.val = 0 := by omega
    have hne_ij : i ≠ j := fun h => by rw [h] at hij; exact Nat.lt_irrefl _ hij
    simp [hi, hj, hne_ij]
  have hbL : IsLabeledRiordanGraph 2 ⊥ := hbot ▸ riordanGraph_isLabeled (by simp)
  have htL : IsLabeledRiordanGraph 2 ⊤ := htop ▸ riordanGraph_isLabeled (by simp)
  refine ⟨hne, ⟨hbL, ?_⟩, ⟨htL, ?_⟩⟩
  · rw [compl_bot]
    exact htL
  · rw [compl_top]
    exact hbL

/-- Boundary classification at `n = 3`:
1. The four graphs `G₃(0, 0)`, `G₃(X, 0)`, `G₃(1 + X, X)`, and `G₃(1, X)` are complement-closed
   labeled Riordan graphs, paired by `(G₃(0, 0))ᶜ = G₃(1 + X, X)` and `(G₃(X, 0))ᶜ = G₃(1, X)`.
2. The remaining two labeled Riordan graphs `G₃(1, 0)` and `G₃(1 + X, 0)` have `g₀ = 1` and
   their complements are NOT labeled Riordan graphs (`a(3) = 4 < 6 = L(3)`). -/
theorem fin3_boundary_classification :
    (riordanGraph 3 0 0)ᶜ = riordanGraph 3 (1 + PowerSeries.X) PowerSeries.X ∧
    (riordanGraph 3 PowerSeries.X 0)ᶜ = riordanGraph 3 1 PowerSeries.X ∧
    ¬ IsLabeledRiordanGraph 3 (riordanGraph 3 1 0)ᶜ ∧
    ¬ IsLabeledRiordanGraph 3 (riordanGraph 3 (1 + PowerSeries.X) 0)ᶜ := by
  have hc1 : (riordanGraph 3 0 0)ᶜ = riordanGraph 3 (1 + PowerSeries.X) PowerSeries.X := by
    rw [compl_eq_riordanGraph_iff (by simp) PowerSeries.coeff_zero_X]
    intro c hc d hd
    have hcases : (c = 0 ∨ c = 1) ∧ (d = 0 ∨ d = 1) := by omega
    rcases hcases with ⟨rfl | rfl, rfl | rfl⟩ <;>
      simp [add_mul, PowerSeries.coeff_X]
  have hc2 : (riordanGraph 3 PowerSeries.X 0)ᶜ = riordanGraph 3 1 PowerSeries.X := by
    rw [compl_eq_riordanGraph_iff (by simp) PowerSeries.coeff_zero_X]
    intro c hc d hd
    have hcases : (c = 0 ∨ c = 1) ∧ (d = 0 ∨ d = 1) := by omega
    rcases hcases with ⟨rfl | rfl, rfl | rfl⟩ <;>
      simp [PowerSeries.coeff_X, zmod2_add_self]
  have hfail : ∀ a : ZMod 2,
      ¬ IsLabeledRiordanGraph 3 (riordanGraph 3 (1 + PowerSeries.C a * PowerSeries.X) 0)ᶜ := by
    intro a hL
    rw [compl_isLabeledRiordan_iff (by simp)] at hL
    obtain ⟨g', f', hf'0, hcols⟩ := hL
    have h0 := hcols 0 (by omega) 0 (by omega)
    simp only [pow_zero, mul_one, map_add, coeff_uSeries, PowerSeries.coeff_one, ite_true,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X, mul_zero, add_zero, zmod2_add_self] at h0
    have h1 := hcols 1 (by omega) 1 (by omega)
    have hgf1 : PowerSeries.coeff 1 (g' * f') = 0 := by
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun x y => PowerSeries.coeff x g' * PowerSeries.coeff y f') 1]
      simp [Finset.sum_range_succ, h0, hf'0]
    rw [pow_one, pow_one, pow_one, mul_zero, add_zero, hgf1,
      PowerSeries.coeff_succ_mul_X 0 uSeries, coeff_uSeries] at h1
    exact zero_ne_one h1
  refine ⟨hc1, hc2, ?_, ?_⟩
  · simpa using hfail 0
  · simpa using hfail 1

/-- Boundary witnesses at `n = 4` (`SCOPING-S012.md` §1.3 & §2.3):
1. First non-Appell complement-closed pair: `(G₄(X, 0))ᶜ = G₄(1 + X^2, X + X^2)`, so `G₄(X, 0)` is
   complement-closed, while `G₄(X, 0)` is NOT Appell (`¬ ∃ g, G₄(X, 0) = G₄(g, X)`).
2. Cheon et al. (2019, §2.6) witness: `G₄(1 + X^2, X^2)` is a labeled Riordan graph whose
   same-labeling complement on `Fin 4` is NOT a labeled Riordan graph. -/
theorem fin4_first_non_appell_and_cheon :
    (riordanGraph 4 PowerSeries.X 0)ᶜ =
      riordanGraph 4 (1 + PowerSeries.X ^ 2) (PowerSeries.X + PowerSeries.X ^ 2) ∧
    (¬ ∃ g : PS, riordanGraph 4 PowerSeries.X 0 = riordanGraph 4 g PowerSeries.X) ∧
    ¬ IsLabeledRiordanGraph 4 (riordanGraph 4 (1 + PowerSeries.X ^ 2) (PowerSeries.X ^ 2))ᶜ := by
  have hf_pair0 : PowerSeries.coeff 0 (PowerSeries.X + PowerSeries.X ^ 2 : PS) = 0 := by
    simp
  have hpair : (riordanGraph 4 PowerSeries.X 0)ᶜ =
      riordanGraph 4 (1 + PowerSeries.X ^ 2) (PowerSeries.X + PowerSeries.X ^ 2) := by
    rw [compl_eq_riordanGraph_iff (by simp) hf_pair0]
    have hexp2 : (PowerSeries.X + PowerSeries.X ^ 2 : PS) ^ 2 =
        PowerSeries.X ^ 2 + PowerSeries.X ^ 4 := by
      rw [ps_add_sq, ← pow_mul]
    intro c hc d hd
    have hcases : (c = 0 ∨ c = 1 ∨ c = 2) ∧ (d = 0 ∨ d = 1 ∨ d = 2) := by omega
    rcases hcases with ⟨rfl | rfl | rfl, rfl | rfl | rfl⟩ <;>
      simp [hexp2, coeff_uSeries_mul_X_pow, add_mul, mul_add, ← pow_add,
        PowerSeries.coeff_X, PowerSeries.coeff_X_pow, zmod2_add_self]
  have hnonAppell : ¬ ∃ g : PS, riordanGraph 4 PowerSeries.X 0 = riordanGraph 4 g PowerSeries.X := by
    rintro ⟨g, hg⟩
    have hcols := (riordanGraph_eq_iff (by simp) PowerSeries.coeff_zero_X).mp hg
    have h0 := hcols 0 (by omega) 1 (by omega)
    simp only [pow_zero, mul_one, PowerSeries.coeff_one_X] at h0
    have h1 := hcols 1 (by omega) 2 (by omega)
    rw [pow_one, pow_one, mul_zero, map_zero, PowerSeries.coeff_succ_mul_X 1 g, ← h0] at h1
    exact zero_ne_one h1
  have hcheon : ¬ IsLabeledRiordanGraph 4
      (riordanGraph 4 (1 + PowerSeries.X ^ 2) (PowerSeries.X ^ 2))ᶜ := by
    have hf2_0 : PowerSeries.coeff 0 (PowerSeries.X ^ 2 : PS) = 0 := by
      simp [PowerSeries.coeff_X_pow]
    intro hL
    rw [compl_isLabeledRiordan_iff hf2_0] at hL
    obtain ⟨g', f', _, hcols⟩ := hL
    have h0 : EqMod 3 g' (uSeries + (1 + PowerSeries.X ^ 2)) := by
      simpa using hcols 0 (by omega)
    have h1 : EqMod 3 (g' * f')
        (uSeries * PowerSeries.X + (1 + PowerSeries.X ^ 2) * PowerSeries.X ^ 2) := by
      simpa using hcols 1 (by omega)
    have h2 : EqMod 3 (g' * f' ^ 2)
        (uSeries * PowerSeries.X ^ 2 + (1 + PowerSeries.X ^ 2) * (PowerSeries.X ^ 2) ^ 2) :=
      hcols 2 (by omega)
    have h2g := EqMod.mul h0 h2
    have h1sq := EqMod.pow h1 2
    rw [show g' * (g' * f' ^ 2) = (g' * f') ^ 2 by ring] at h2g
    have hrel := (EqMod.symm h2g).trans h1sq
    have hsum := EqMod.add hrel
      (EqMod.refl 3 ((uSeries * PowerSeries.X + (1 + PowerSeries.X ^ 2) * PowerSeries.X ^ 2) ^ 2))
    rw [ps_add_self, delta_identity] at hsum
    have hmul := EqMod.mul (EqMod.refl 3 (1 + PowerSeries.X)) hsum
    rw [← mul_assoc, one_add_X_mul_uSeries, one_mul, mul_zero] at hmul
    have hc2 := hmul 2 (by omega)
    have hexp : (1 + PowerSeries.X ^ 2 : PS) * (PowerSeries.X ^ 2 + PowerSeries.X) ^ 2 =
        PowerSeries.X ^ 2 + PowerSeries.X ^ 6 := by
      rw [ps_add_sq, ← pow_mul]
      calc
        (1 + PowerSeries.X ^ 2 : PS) * (PowerSeries.X ^ 4 + PowerSeries.X ^ 2)
          = PowerSeries.X ^ 2 + (PowerSeries.X ^ 4 + PowerSeries.X ^ 4) + PowerSeries.X ^ 6 := by ring
        _ = PowerSeries.X ^ 2 + PowerSeries.X ^ 6 := by rw [ps_add_self, add_zero]
    rw [hexp, map_add, PowerSeries.coeff_X_pow_self, PowerSeries.coeff_X_pow,
      ite_eq_right (by omega : (2 : ℕ) ≠ 6), add_zero, map_zero] at hc2
    exact one_ne_zero hc2
  exact ⟨hpair, hnonAppell, hcheon⟩

/-- Refutation of the heuristic "plus 4 fixed families" shift (`SCOPING-S012.md` §2.2(1)):
there is NO integer `c ∈ ℤ` satisfying `a(n) - c = 8 * (a(n - 2) - c)` for all `n ≥ 3`
(the unique rational fixed point is `c = 4/7 ∉ ℤ`). -/
theorem no_integer_fixed_point_shift :
    ¬ ∃ c : ℤ, ∀ n : ℕ, 3 ≤ n →
      (complementClosedRiordanCount n : ℤ) - c =
        8 * ((complementClosedRiordanCount (n - 2) : ℤ) - c) := by
  rintro ⟨c, hc⟩
  have h3 := hc 3 (by omega)
  have ha3 : complementClosedRiordanCount 3 = 4 := by
    rw [complementClosed_riordan_count_eq 3 (by omega),
      show (3 : ℕ) - 2 = 1 from rfl, complementClosed_riordan_count_one]
  rw [ha3, show (3 : ℕ) - 2 = 1 from rfl, complementClosed_riordan_count_one] at h3
  omega

end SeamC.A401496
