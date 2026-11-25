import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Nth
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Seam B Entry A186424 (OEIS A186424): Peter Bala's Rogers–Fine Polynomial Family

Formalizes and proves Peter Bala's February 13, 2021 conjectural `N`-parameterized
generating-function family on `OEIS A186424` (`%F` lines 20–25, live revision `#52 Dec 29 2025`;
primary `%N` chain `A186421` → `A186423` → `A186424`) against the frozen target contract
`PIN-A186424.md` v1 (`sha256: f6ae3e2474f1dc176d46947879978a778ee914d8178a2acce70cab83860d7757`;
`Statement.lean sha256: 2978bbb21eab104406c097096a53d2bff4bf94caaa3b83d9790272cb2b014d39`,
single adjudicated `N = 0` boundary correction `Q_0 = 1`, zero delta for all `N ≥ 1`),
completely self-contained in `ℤ[X]` and `ℤ⟦X⟧` via `Step 0 + Links 1–3`:

1. **Step 0 (`a186424_closed_form`)**: Mod-4 block summation of `a186421` gives closed forms
   for `a186423` on all four residue classes mod 4, identifying `{j | Odd (a186423 j)}` with
   `{j | j % 4 = 1 ∨ j % 4 = 2}` and pinning `Nat.nth` via
   `Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn` to yield `StrictMono a186424`,
   `a186424 (2 * r) = 6 * r ^ 2 + 4 * r + 1`, and `a186424 (2 * r + 1) = 6 * r ^ 2 + 8 * r + 3`.
2. **Link 1 (Positive-valuation Rogers–Fine telescoping in `ℤ⟦X⟧`)**: Specialization at
   `q = X^2, α = 0, β = X^3, τ = -X` via the unit-clearing step
   `rfSummand M (s + 1) + X^(2M+1) * rfSummand M s = (1 + X^(2M+1)) * rfSummand (M + 1) s`,
   bypassing double-sum Fubini swaps to prove
   `S(X) = 1 - X * ∑_{m ≥ 0} (-1)^m X^{2m(m+1)} / ∏_{k=1}^{m+1} (1 - X^{4k-2})`.
3. **Link 2 (Rogers's order-3 false-theta identity and `a186424_base_series`)**: Direct formal
   telescoping in `ℤ⟦X⟧` (with `y = X^2`) on `kRem M` with exponent
   `2 * (r(r+1) + 3M^2 + 4Mr + 2M)` proves
   `kRem M - kRem (M + 1) = (-1)^M (X^{6M^2 + 4M} + X^{6M^2 + 8M + 2})`, closing Bala's base
   identity `S(X) = F(X)` (classically equivalent to Andrews 1979 / Chen 2014 Eq. 22 /
   Rogers 1917 Eq. 5.3.2, proved here purely from Mathlib primitives).
4. **Link 3 (Shift-and-cancel induction for all `N ≥ 0` and polynomial structure)**:
   Proves `(1 + X^(2N+1)) * S_N(X) = -X^(N+1) + S_{N+1}(X)`, closing `a186424Poly_closed_form`,
   `a186424Poly_empirical_values`, `a186424Poly_degree_and_monic`, `a186424_family_explicit`,
   `a186424_family` (`∃!`), and `a186424_family_exists`.
5. **Diagnostic extensions**: Verifies `Q_5(X)`, `Q_6(X)` with its first `|coeff| > 1` term
   `-2 * X^13`, formal refutation of Bala's printed `P(0, X) = 0` slip at constant term, and
   spot checks of `a186424` on OEIS terms `0..19`.
-/

namespace Mathproofs.A186424

open scoped BigOperators Classical Polynomial PowerSeries PowerSeries.WithPiTopology

noncomputable section

/-! ### Pinned Target Definitions (`PIN-A186424.md` v1) -/

/-- Primary `%N` `OEIS A186421` sequence (even numbers interleaved with repeated odd numbers,
offset `0`). -/
def a186421 (n : ℕ) : ℕ :=
  if Even n then n else 2 * (n / 4) + 1

/-- Primary `%N` `OEIS A186423` sequence (partial sums of `A186421`, offset `0`). -/
def a186423 (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), a186421 i

/-- Primary `%N` `OEIS A186424` sequence (odd terms in `A186423` in order, offset `0`). -/
def a186424 (n : ℕ) : ℕ :=
  a186423 (Nat.nth (fun j ↦ Odd (a186423 j)) n)

/-- Formal power series `F(X) = 1 - X - X^3 + X^11 + X^17 - X^33 - X^43 + ...` in `ℤ⟦X⟧`
defined directly from `a186424`. -/
def a186424FalseTheta : ℤ⟦X⟧ :=
  PowerSeries.mk fun d ↦
    if d = 0 then 1
    else if h : ∃ m : ℕ, a186424 m = d then (-1 : ℤ) ^ (h.choose / 2 + 1)
    else 0

/-- Explicit polynomial family `Q_N(X) ∈ ℤ[X]` pinned for all `N : ℕ` by `Q_0(X) = 1` and
`Q_{N+1}(X) = (1 + X^(2N+1)) * Q_N(X) - X^(N+1)`. -/
def a186424Poly : ℕ → ℤ[X]
  | 0 => 1
  | N + 1 => (1 + Polynomial.X ^ (2 * N + 1)) * a186424Poly N - Polynomial.X ^ (N + 1)

/-! ### Section 1: Finite-Interval, Unit-Reciprocal, and Locally-Finite `HasSum` Helpers -/

private lemma finset_Icc_succ_right {a b : ℕ} (h : a ≤ b + 1) :
    Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

private lemma finset_Icc_of_gt {a b : ℕ} (h : b < a) :
    Finset.Icc a b = ∅ := by
  ext x
  simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false]
  omega

private abbrev inv1 (φ : ℤ⟦X⟧) : ℤ⟦X⟧ :=
  PowerSeries.invOfUnit φ (1 : ℤˣ)

private lemma constantCoeff_X_pow_pos {k : ℕ} (hk : 0 < k) :
    PowerSeries.constantCoeff ((PowerSeries.X : ℤ⟦X⟧) ^ k) = 0 := by
  cases k with
  | zero => omega
  | succ m => simp [pow_succ]

private lemma constantCoeff_one_add_X_pow {k : ℕ} (hk : 0 < k) :
    PowerSeries.constantCoeff (1 + (PowerSeries.X : ℤ⟦X⟧) ^ k) = 1 := by
  rw [map_add, map_one, constantCoeff_X_pow_pos hk, add_zero]

private lemma constantCoeff_one_sub_X_pow {k : ℕ} (hk : 0 < k) :
    PowerSeries.constantCoeff (1 - (PowerSeries.X : ℤ⟦X⟧) ^ k) = 1 := by
  rw [map_sub, map_one, constantCoeff_X_pow_pos hk, sub_zero]

private lemma constantCoeff_prod_one_add {ι : Type*} (s : Finset ι) (e : ι → ℕ)
    (he : ∀ i ∈ s, 0 < e i) :
    PowerSeries.constantCoeff (∏ i ∈ s, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ e i)) = 1 := by
  rw [map_prod]
  exact Finset.prod_eq_one fun i hi ↦ constantCoeff_one_add_X_pow (he i hi)

private lemma constantCoeff_prod_one_sub {ι : Type*} (s : Finset ι) (e : ι → ℕ)
    (he : ∀ i ∈ s, 0 < e i) :
    PowerSeries.constantCoeff (∏ i ∈ s, (1 - (PowerSeries.X : ℤ⟦X⟧) ^ e i)) = 1 := by
  rw [map_prod]
  exact Finset.prod_eq_one fun i hi ↦ constantCoeff_one_sub_X_pow (he i hi)

private lemma mul_inv1 {φ : ℤ⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 1) :
    φ * inv1 φ = 1 :=
  PowerSeries.mul_invOfUnit φ (1 : ℤˣ) (by simpa using hφ)

private lemma inv1_mul {φ : ℤ⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 1) :
    inv1 φ * φ = 1 :=
  PowerSeries.invOfUnit_mul φ (1 : ℤˣ) (by simpa using hφ)

private lemma inv1_one : inv1 (1 : ℤ⟦X⟧) = 1 := by
  have h := inv1_mul (φ := (1 : ℤ⟦X⟧)) (map_one _)
  simpa using h

private lemma inv1_mul_distrib {φ ψ : ℤ⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 1) (hψ : PowerSeries.constantCoeff ψ = 1) :
    inv1 (φ * ψ) = inv1 φ * inv1 ψ := by
  have hφψ : PowerSeries.constantCoeff (φ * ψ) = 1 := by
    rw [map_mul, hφ, hψ, mul_one]
  calc
    inv1 (φ * ψ) = inv1 (φ * ψ) * ((φ * ψ) * (inv1 φ * inv1 ψ)) := by
      have : (φ * ψ) * (inv1 φ * inv1 ψ) = 1 := by
        calc
          (φ * ψ) * (inv1 φ * inv1 ψ) = (φ * inv1 φ) * (ψ * inv1 ψ) := by ring
          _ = 1 * 1 := by rw [mul_inv1 hφ, mul_inv1 hψ]
          _ = 1 := mul_one 1
      rw [this, mul_one]
    _ = (inv1 (φ * ψ) * (φ * ψ)) * (inv1 φ * inv1 ψ) := by ring
    _ = inv1 φ * inv1 ψ := by rw [inv1_mul hφψ, one_mul]

private lemma mul_inv1_cancel_right {φ ψ : ℤ⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 1) (hψ : PowerSeries.constantCoeff ψ = 1) :
    ψ * inv1 (φ * ψ) = inv1 φ := by
  rw [inv1_mul_distrib hφ hψ]
  calc
    ψ * (inv1 φ * inv1 ψ) = inv1 φ * (ψ * inv1 ψ) := by ring
    _ = inv1 φ * 1 := by rw [mul_inv1 hψ]
    _ = inv1 φ := mul_one _

private lemma mul_inv1_cancel_left {φ ψ : ℤ⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 1) (hψ : PowerSeries.constantCoeff ψ = 1) :
    φ * inv1 (φ * ψ) = inv1 ψ := by
  rw [mul_comm φ ψ]
  exact mul_inv1_cancel_right hψ hφ

private lemma coeff_X_pow_mul_eq_zero {e d : ℕ} (hd : d < e) (ψ : ℤ⟦X⟧) :
    PowerSeries.coeff d ((PowerSeries.X : ℤ⟦X⟧) ^ e * ψ) = 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  have hle : ¬ e ≤ d := by omega
  simp [hle]

private lemma hasSum_mk_of_coeff_vanish (f : ℕ → ℤ⟦X⟧) (B : ℕ → ℕ)
    (hvanish : ∀ d m : ℕ, B d ≤ m → PowerSeries.coeff d (f m) = 0) :
    HasSum f (PowerSeries.mk fun d ↦ ∑ m ∈ Finset.range (B d), PowerSeries.coeff d (f m)) := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  rw [PowerSeries.coeff_mk]
  refine hasSum_sum_of_ne_finset_zero fun m hm ↦ ?_
  rw [Finset.mem_range, not_lt] at hm
  exact hvanish d m hm

private lemma hasSum_of_sub_eq_and_coeff_zero (R t : ℕ → ℤ⟦X⟧)
    (hstep : ∀ M : ℕ, R M - R (M + 1) = t M)
    (hzero : ∀ d M : ℕ, d < M → PowerSeries.coeff d (R M) = 0) :
    HasSum t (R 0) := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  have hfin : HasSum (fun M ↦ PowerSeries.coeff d (t M))
      (∑ M ∈ Finset.range (d + 1), PowerSeries.coeff d (t M)) := by
    refine hasSum_sum_of_ne_finset_zero fun M hM ↦ ?_
    rw [Finset.mem_range, not_lt] at hM
    rw [← hstep M, map_sub, hzero d M (by omega), hzero d (M + 1) (by omega), sub_zero]
  have htel : ∑ M ∈ Finset.range (d + 1), PowerSeries.coeff d (t M) =
      PowerSeries.coeff d (R 0) := by
    have hcongr : ∀ M ∈ Finset.range (d + 1),
        PowerSeries.coeff d (t M) =
          PowerSeries.coeff d (R M) - PowerSeries.coeff d (R (M + 1)) := by
      intro M _
      rw [← hstep M, map_sub]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_range_sub' (fun M ↦ PowerSeries.coeff d (R M)),
      hzero d (d + 1) (by omega), sub_zero]
  rwa [htel] at hfin

/-! ### Section 2: Step 0 — Primary `%N` Chain (`A186421` → `A186423` → `A186424`) -/

private lemma a186421_four_mul (r : ℕ) : a186421 (4 * r) = 4 * r := by
  unfold a186421
  have hev : Even (4 * r) := ⟨2 * r, by ring⟩
  simp [hev]

private lemma a186421_four_mul_add_one (r : ℕ) : a186421 (4 * r + 1) = 2 * r + 1 := by
  unfold a186421
  have hnot : ¬ Even (4 * r + 1) := by
    rw [Nat.not_even_iff_odd]
    exact ⟨2 * r, by ring⟩
  have hdiv : (4 * r + 1) / 4 = r := by omega
  simp [hnot, hdiv]

private lemma a186421_four_mul_add_two (r : ℕ) : a186421 (4 * r + 2) = 4 * r + 2 := by
  unfold a186421
  have hev : Even (4 * r + 2) := ⟨2 * r + 1, by ring⟩
  simp [hev]

private lemma a186421_four_mul_add_three (r : ℕ) : a186421 (4 * r + 3) = 2 * r + 1 := by
  unfold a186421
  have hnot : ¬ Even (4 * r + 3) := by
    rw [Nat.not_even_iff_odd]
    exact ⟨2 * r + 1, by ring⟩
  have hdiv : (4 * r + 3) / 4 = r := by omega
  simp [hnot, hdiv]

private lemma a186421_pos {n : ℕ} (hn : 0 < n) : 0 < a186421 n := by
  unfold a186421
  split_ifs <;> omega

private lemma a186423_succ (n : ℕ) : a186423 (n + 1) = a186423 n + a186421 (n + 1) := by
  unfold a186423
  rw [Finset.sum_range_succ]

private lemma a186423_strictMono : StrictMono a186423 := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  rw [a186423_succ]
  have hpos : 0 < a186421 (n + 1) := a186421_pos (by omega)
  omega

private lemma a186423_four_mul (r : ℕ) : a186423 (4 * r) = 6 * r ^ 2 + 2 * r := by
  induction r with
  | zero =>
    unfold a186423
    simp [a186421]
  | succ r ih =>
    have h4 : 4 * (r + 1) = 4 * r + 3 + 1 := by omega
    rw [h4, a186423_succ, a186423_succ, a186423_succ, a186423_succ, ih,
      a186421_four_mul_add_one, a186421_four_mul_add_two, a186421_four_mul_add_three]
    have h4' : 4 * r + 3 + 1 = 4 * (r + 1) := by omega
    rw [h4', a186421_four_mul]
    ring

private lemma a186423_four_mul_add_one (r : ℕ) :
    a186423 (4 * r + 1) = 6 * r ^ 2 + 4 * r + 1 := by
  rw [a186423_succ, a186423_four_mul, a186421_four_mul_add_one]
  ring

private lemma a186423_four_mul_add_two (r : ℕ) :
    a186423 (4 * r + 2) = 6 * r ^ 2 + 8 * r + 3 := by
  rw [show 4 * r + 2 = (4 * r + 1) + 1 by omega, a186423_succ, a186423_four_mul_add_one,
    show 4 * r + 1 + 1 = 4 * r + 2 by omega, a186421_four_mul_add_two]
  ring

private lemma a186423_four_mul_add_three (r : ℕ) :
    a186423 (4 * r + 3) = 6 * r ^ 2 + 10 * r + 4 := by
  rw [show 4 * r + 3 = (4 * r + 2) + 1 by omega, a186423_succ, a186423_four_mul_add_two,
    show 4 * r + 2 + 1 = 4 * r + 3 by omega, a186421_four_mul_add_three]
  ring

private lemma odd_a186423_iff (j : ℕ) : Odd (a186423 j) ↔ j % 4 = 1 ∨ j % 4 = 2 := by
  set r := j / 4
  have hmod : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
  rcases hmod with h0 | h1 | h2 | h3
  · have hj : j = 4 * r := by omega
    rw [hj, a186423_four_mul]
    have hev : Even (6 * r ^ 2 + 2 * r) := ⟨3 * r ^ 2 + r, by ring⟩
    simp [Nat.not_odd_iff_even.mpr hev]
  · have hj : j = 4 * r + 1 := by omega
    rw [hj, a186423_four_mul_add_one]
    have hodd : Odd (6 * r ^ 2 + 4 * r + 1) := ⟨3 * r ^ 2 + 2 * r, by ring⟩
    simp [hodd]
  · have hj : j = 4 * r + 2 := by omega
    rw [hj, a186423_four_mul_add_two]
    have hodd : Odd (6 * r ^ 2 + 8 * r + 3) := ⟨3 * r ^ 2 + 4 * r + 1, by ring⟩
    simp [hodd]
  · have hj : j = 4 * r + 3 := by omega
    rw [hj, a186423_four_mul_add_three]
    have hev : Even (6 * r ^ 2 + 10 * r + 4) := ⟨3 * r ^ 2 + 5 * r + 2, by ring⟩
    simp [Nat.not_odd_iff_even.mpr hev]

private def oddIdx (n : ℕ) : ℕ :=
  4 * (n / 2) + n % 2 + 1

private lemma oddIdx_strictMono : StrictMono oddIdx := by
  intro a b hab
  unfold oddIdx
  omega

private lemma oddIdx_mem (n : ℕ) : Odd (a186423 (oddIdx n)) := by
  rw [odd_a186423_iff]
  unfold oddIdx
  omega

private lemma odd_a186423_infinite : (Set.ofPred (fun j ↦ Odd (a186423 j))).Infinite := by
  refine Set.infinite_of_forall_exists_gt fun n ↦ ⟨4 * n + 1, ?_, by omega⟩
  change Odd (a186423 (4 * n + 1))
  rw [odd_a186423_iff]
  omega

private lemma nth_odd_a186423_eq (n : ℕ) :
    Nat.nth (fun j ↦ Odd (a186423 j)) n = oddIdx n := by
  have heq := Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn
    (p := fun j ↦ Odd (a186423 j)) oddIdx
    (by
      intro j hj
      change Odd (a186423 j) at hj
      rw [odd_a186423_iff] at hj
      rcases hj with h1 | h2
      · refine ⟨2 * (j / 4), fun hf ↦ (odd_a186423_infinite hf).elim, ?_⟩
        unfold oddIdx
        omega
      · refine ⟨2 * (j / 4) + 1, fun hf ↦ (odd_a186423_infinite hf).elim, ?_⟩
        unfold oddIdx
        omega)
    (fun m _ ↦ oddIdx_mem m)
    (oddIdx_strictMono.strictMonoOn _)
  exact (heq (fun hf ↦ (odd_a186423_infinite hf).elim)).symm

/-- Explicit quadratic evaluation and strict monotonicity of `A186424`. -/
theorem a186424_closed_form :
    StrictMono a186424 ∧
      ∀ r : ℕ,
        a186424 (2 * r) = 6 * r ^ 2 + 4 * r + 1 ∧
        a186424 (2 * r + 1) = 6 * r ^ 2 + 8 * r + 3 := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    unfold a186424
    rw [nth_odd_a186423_eq, nth_odd_a186423_eq]
    exact a186423_strictMono (oddIdx_strictMono hab)
  · intro r
    unfold a186424
    rw [nth_odd_a186423_eq, nth_odd_a186423_eq]
    have h0 : oddIdx (2 * r) = 4 * r + 1 := by unfold oddIdx; omega
    have h1 : oddIdx (2 * r + 1) = 4 * r + 2 := by unfold oddIdx; omega
    rw [h0, h1, a186423_four_mul_add_one, a186423_four_mul_add_two]
    exact ⟨rfl, rfl⟩

private lemma a186424_pos (m : ℕ) : 0 < a186424 m := by
  have hcl := a186424_closed_form.2 (m / 2)
  rcases Nat.even_or_odd m with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · have := (a186424_closed_form.2 r).1
    rw [show r + r = 2 * r by omega, this]
    omega
  · have := (a186424_closed_form.2 r).2
    rw [this]
    omega

/-! ### Section 3: Link 1 — Positive-Valuation Rogers–Fine Telescoping in `ℤ⟦X⟧` -/

private def rfMinusProd (k : ℕ) : ℤ⟦X⟧ :=
  ∏ i ∈ Finset.range k, (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * i + 3))

private def rfPlusProd (M : ℕ) : ℤ⟦X⟧ :=
  ∏ i ∈ Finset.range M, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * i + 1))

private lemma rfMinusProd_const (k : ℕ) : PowerSeries.constantCoeff (rfMinusProd k) = 1 :=
  constantCoeff_prod_one_sub _ _ (fun _ _ ↦ by omega)

private lemma rfPlusProd_const (M : ℕ) : PowerSeries.constantCoeff (rfPlusProd M) = 1 :=
  constantCoeff_prod_one_add _ _ (fun _ _ ↦ by omega)

private def rfExp (M r : ℕ) : ℕ :=
  2 * M * (M + 1) + (2 * M + 1) * r

private lemma rfExp_shift_r (M s : ℕ) :
    (2 * M + 1) + rfExp M s = rfExp M (s + 1) := by
  unfold rfExp
  ring

private lemma rfExp_step_M (M s : ℕ) :
    rfExp M (s + 1) + (2 * M + 2 * s + 3) = rfExp (M + 1) s := by
  unfold rfExp
  ring

private def rfSummand (M r : ℕ) : ℤ⟦X⟧ :=
  (-1 : ℤ⟦X⟧) ^ (M + r) * (PowerSeries.X : ℤ⟦X⟧) ^ rfExp M r *
    inv1 (rfMinusProd (M + r)) * inv1 (rfPlusProd M)

private lemma rfSummand_vanish (M d r : ℕ) (hr : d + 1 ≤ r) :
    PowerSeries.coeff d (rfSummand M r) = 0 := by
  unfold rfSummand
  have he : d < rfExp M r := by
    unfold rfExp
    have hmul : r ≤ (2 * M + 1) * r := Nat.le_mul_of_pos_left r (by omega)
    omega
  have hrew : (-1 : ℤ⟦X⟧) ^ (M + r) * (PowerSeries.X : ℤ⟦X⟧) ^ rfExp M r *
      inv1 (rfMinusProd (M + r)) * inv1 (rfPlusProd M) =
      (PowerSeries.X : ℤ⟦X⟧) ^ rfExp M r *
        ((-1 : ℤ⟦X⟧) ^ (M + r) * inv1 (rfMinusProd (M + r)) * inv1 (rfPlusProd M)) := by ring
  rw [hrew]
  exact coeff_X_pow_mul_eq_zero he _

private def rfRem (M : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun d ↦ ∑ r ∈ Finset.range (d + 1), PowerSeries.coeff d (rfSummand M r)

private lemma hasSum_rfSummand (M : ℕ) : HasSum (rfSummand M) (rfRem M) :=
  hasSum_mk_of_coeff_vanish (rfSummand M) (fun d ↦ d + 1) (rfSummand_vanish M)

private lemma rf_term_identity (M s : ℕ) :
    rfSummand M (s + 1) + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1) * rfSummand M s =
      (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1)) * rfSummand (M + 1) s := by
  unfold rfSummand
  have hminus_step : inv1 (rfMinusProd (M + s)) =
      (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * (M + s) + 3)) * inv1 (rfMinusProd (M + s + 1)) := by
    have hpr : rfMinusProd (M + s + 1) =
        rfMinusProd (M + s) * (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * (M + s) + 3)) :=
      Finset.prod_range_succ _ (M + s)
    rw [hpr]
    exact (mul_inv1_cancel_right (rfMinusProd_const (M + s))
      (constantCoeff_one_sub_X_pow (by omega))).symm
  have hplus_step : (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1)) * inv1 (rfPlusProd (M + 1)) =
      inv1 (rfPlusProd M) := by
    have hpr : rfPlusProd (M + 1) =
        rfPlusProd M * (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1)) :=
      Finset.prod_range_succ _ M
    rw [hpr]
    exact mul_inv1_cancel_right (rfPlusProd_const M)
      (constantCoeff_one_add_X_pow (by omega))
  have hMs : M + (s + 1) = M + s + 1 := by omega
  have hM1s : M + 1 + s = M + s + 1 := by omega
  rw [hMs, hM1s, hminus_step]
  have hrhs : (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1)) *
      ((-1 : ℤ⟦X⟧) ^ (M + s + 1) * (PowerSeries.X : ℤ⟦X⟧) ^ rfExp (M + 1) s *
        inv1 (rfMinusProd (M + s + 1)) * inv1 (rfPlusProd (M + 1))) =
      (-1 : ℤ⟦X⟧) ^ (M + s + 1) * (PowerSeries.X : ℤ⟦X⟧) ^ rfExp (M + 1) s *
        inv1 (rfMinusProd (M + s + 1)) *
        ((1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1)) * inv1 (rfPlusProd (M + 1))) := by ring
  rw [hrhs, hplus_step, ← rfExp_step_M M s]
  have hlhs_exp : (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1) *
      ((-1 : ℤ⟦X⟧) ^ (M + s) * (PowerSeries.X : ℤ⟦X⟧) ^ rfExp M s *
        ((1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * (M + s) + 3)) * inv1 (rfMinusProd (M + s + 1))) *
        inv1 (rfPlusProd M)) =
      (-1 : ℤ⟦X⟧) ^ (M + s) * ((PowerSeries.X : ℤ⟦X⟧) ^ ((2 * M + 1) + rfExp M s)) *
        (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2 * s + 3)) *
        inv1 (rfMinusProd (M + s + 1)) * inv1 (rfPlusProd M) := by
    rw [pow_add]
    have : 2 * (M + s) + 3 = 2 * M + 2 * s + 3 := by omega
    rw [this]
    ring
  rw [hlhs_exp, rfExp_shift_r M s]
  simp only [pow_add, pow_one]
  ring

private lemma rfRem_sub_succ (M : ℕ) :
    rfRem M - rfRem (M + 1) =
      (-1 : ℤ⟦X⟧) ^ M * (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M * (M + 1)) *
        inv1 (rfMinusProd M) * inv1 (rfPlusProd (M + 1)) := by
  have hshift : HasSum (fun s ↦ rfSummand M (s + 1)) (rfRem M - rfSummand M 0) := by
    have hM := hasSum_rfSummand M
    rw [← hasSum_nat_add_iff' 1] at hM
    simpa [Finset.sum_range_one] using hM
  have hmul := (hasSum_rfSummand M).mul_left ((PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1))
  have hsum_lhs := hshift.add hmul
  have hsum_rhs := (hasSum_rfSummand (M + 1)).mul_left (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1))
  have hcongr : (fun s ↦ rfSummand M (s + 1) + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1) * rfSummand M s) =
      (fun s ↦ (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1)) * rfSummand (M + 1) s) := by
    funext s
    exact rf_term_identity M s
  rw [hcongr] at hsum_lhs
  have heq := hsum_lhs.unique hsum_rhs
  have hunit : (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1)) * (rfRem M - rfRem (M + 1)) =
      rfSummand M 0 := by
    calc
      (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1)) * (rfRem M - rfRem (M + 1))
          = (rfRem M - rfSummand M 0 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1) * rfRem M) -
              (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1)) * rfRem (M + 1) + rfSummand M 0 := by
            ring
      _ = 0 + rfSummand M 0 := by rw [heq, sub_self]
      _ = rfSummand M 0 := zero_add _
  have hc : PowerSeries.constantCoeff (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1)) = 1 :=
    constantCoeff_one_add_X_pow (by omega)
  have hdiv : rfRem M - rfRem (M + 1) =
      rfSummand M 0 * inv1 (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1)) := by
    calc
      rfRem M - rfRem (M + 1)
          = (inv1 (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1)) *
              (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1))) * (rfRem M - rfRem (M + 1)) := by
            rw [inv1_mul hc, one_mul]
      _ = inv1 (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1)) *
            ((1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1)) * (rfRem M - rfRem (M + 1))) := by ring
      _ = rfSummand M 0 * inv1 (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1)) := by
            rw [hunit, mul_comm]
  rw [hdiv]
  unfold rfSummand rfExp
  simp only [Nat.add_zero, mul_zero]
  have hplus_mul : inv1 (rfPlusProd M) * inv1 (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1)) =
      inv1 (rfPlusProd (M + 1)) := by
    have hpr : rfPlusProd (M + 1) =
        rfPlusProd M * (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1)) :=
      Finset.prod_range_succ _ M
    rw [hpr, inv1_mul_distrib (rfPlusProd_const M) hc]
  calc
    (-1 : ℤ⟦X⟧) ^ M * (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M * (M + 1)) * inv1 (rfMinusProd M) *
        inv1 (rfPlusProd M) * inv1 (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1))
        = (-1 : ℤ⟦X⟧) ^ M * (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M * (M + 1)) * inv1 (rfMinusProd M) *
            (inv1 (rfPlusProd M) * inv1 (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 1))) := by ring
    _ = (-1 : ℤ⟦X⟧) ^ M * (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M * (M + 1)) * inv1 (rfMinusProd M) *
          inv1 (rfPlusProd (M + 1)) := by rw [hplus_mul]

private lemma rfRem_coeff_zero {d M : ℕ} (hdM : d < M) :
    PowerSeries.coeff d (rfRem M) = 0 := by
  rw [rfRem, PowerSeries.coeff_mk]
  refine Finset.sum_eq_zero fun r _ ↦ ?_
  unfold rfSummand
  have he : d < rfExp M r := by
    unfold rfExp
    have h1 : M ≤ 2 * M * (M + 1) := by nlinarith
    omega
  have hrew : (-1 : ℤ⟦X⟧) ^ (M + r) * (PowerSeries.X : ℤ⟦X⟧) ^ rfExp M r *
      inv1 (rfMinusProd (M + r)) * inv1 (rfPlusProd M) =
      (PowerSeries.X : ℤ⟦X⟧) ^ rfExp M r *
        ((-1 : ℤ⟦X⟧) ^ (M + r) * inv1 (rfMinusProd (M + r)) * inv1 (rfPlusProd M)) := by ring
  rw [hrew]
  exact coeff_X_pow_mul_eq_zero he _

private lemma one_sub_X_mul_rfMinusProd (m : ℕ) :
    (1 - (PowerSeries.X : ℤ⟦X⟧)) * rfMinusProd m =
      ∏ k ∈ Finset.Icc 1 (m + 1), (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1)) := by
  induction m with
  | zero =>
    simp [rfMinusProd]
  | succ m ih =>
    rw [rfMinusProd, Finset.prod_range_succ, ← mul_assoc, ← rfMinusProd, ih,
      finset_Icc_succ_right (by omega : 1 ≤ m + 1 + 1), Finset.prod_insert (by simp)]
    have hexp : 2 * (m + 1 + 1) - 1 = 2 * m + 3 := by omega
    rw [hexp, mul_comm]

/-! ### Section 4: Link 2 — Rogers's Order-3 False-Theta Identity in `ℤ⟦X⟧` -/

private def kExp (M r : ℕ) : ℕ :=
  2 * (r * (r + 1) + 3 * M ^ 2 + 4 * M * r + 2 * M)

private def kProd (M r : ℕ) : ℤ⟦X⟧ :=
  ∏ i ∈ Finset.range (r + 1), (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (4 * (M + i) + 2))

private lemma kProd_const (M r : ℕ) : PowerSeries.constantCoeff (kProd M r) = 1 :=
  constantCoeff_prod_one_sub _ _ (fun _ _ ↦ by omega)

private lemma kProd_succ_right (M r : ℕ) :
    kProd M (r + 1) = kProd M r * (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (4 * (M + r + 1) + 2)) := by
  unfold kProd
  rw [Finset.prod_range_succ]
  have : M + (r + 1) = M + r + 1 := by omega
  rw [this]

private lemma kProd_succ_left (M s : ℕ) :
    kProd M (s + 1) = (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (4 * M + 2)) * kProd (M + 1) s := by
  unfold kProd
  rw [Finset.prod_range_succ', mul_comm]
  refine congrArg₂ (· * ·) ?_ ?_
  · simp
  · refine Finset.prod_congr rfl fun i _ ↦ ?_
    have : 4 * (M + (i + 1)) + 2 = 4 * (M + 1 + i) + 2 := by omega
    rw [this]

private lemma minus_plus_prod_eq_kProd (m : ℕ) :
    ((1 - (PowerSeries.X : ℤ⟦X⟧)) * rfMinusProd m) * rfPlusProd (m + 1) = kProd 0 m := by
  induction m with
  | zero =>
    simp only [rfMinusProd, rfPlusProd, kProd, Finset.prod_range_zero, Finset.prod_range_succ,
      mul_one, one_mul, Nat.add_zero]
    ring
  | succ m ih =>
    have h1 : rfMinusProd (m + 1) = rfMinusProd m * (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * m + 3)) :=
      Finset.prod_range_succ _ m
    have h2 : rfPlusProd (m + 2) = rfPlusProd (m + 1) * (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * m + 3)) := by
      have := Finset.prod_range_succ (fun i ↦ 1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * i + 1)) (m + 1)
      simpa [rfPlusProd, show 2 * (m + 1) + 1 = 2 * m + 3 by omega] using this
    have h3 : kProd 0 (m + 1) =
        kProd 0 m * (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (4 * m + 6)) := by
      rw [kProd_succ_right 0 m, show 4 * (0 + m + 1) + 2 = 4 * m + 6 by omega]
    have hdiff : (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * m + 3)) *
        (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * m + 3)) =
        1 - (PowerSeries.X : ℤ⟦X⟧) ^ (4 * m + 6) := by
      have hexp : 4 * m + 6 = (2 * m + 3) + (2 * m + 3) := by omega
      rw [hexp, pow_add]
      ring
    rw [h1, h2, h3, ← ih]
    calc
      (1 - PowerSeries.X) * (rfMinusProd m * (1 - PowerSeries.X ^ (2 * m + 3))) *
          (rfPlusProd (m + 1) * (1 + PowerSeries.X ^ (2 * m + 3)))
          = ((1 - PowerSeries.X) * rfMinusProd m * rfPlusProd (m + 1)) *
              ((1 - PowerSeries.X ^ (2 * m + 3)) * (1 + PowerSeries.X ^ (2 * m + 3))) := by ring
      _ = ((1 - PowerSeries.X) * rfMinusProd m * rfPlusProd (m + 1)) *
            (1 - PowerSeries.X ^ (4 * m + 6)) := by rw [hdiff]

private lemma kExp_succ_left (M s : ℕ) :
    kExp (M + 1) s = kExp M (s + 1) + (4 * (M + s + 1) + 2) := by
  unfold kExp
  ring

private lemma kExp_add_first (M s : ℕ) :
    kExp (M + 1) s + (4 * M + 2) = kExp M (s + 2) := by
  unfold kExp
  ring

private def kSummand (M r : ℕ) : ℤ⟦X⟧ :=
  (-1 : ℤ⟦X⟧) ^ (M + r) * (PowerSeries.X : ℤ⟦X⟧) ^ kExp M r * inv1 (kProd M r)

private def kAux (M s : ℕ) : ℤ⟦X⟧ :=
  (-1 : ℤ⟦X⟧) ^ (M + s + 1) * (PowerSeries.X : ℤ⟦X⟧) ^ kExp M (s + 1) * inv1 (kProd M s)

private lemma kSummand_vanish (M d r : ℕ) (hr : d + 1 ≤ r) :
    PowerSeries.coeff d (kSummand M r) = 0 := by
  unfold kSummand
  have he : d < kExp M r := by
    unfold kExp
    have h1 : r ≤ r * (r + 1) := Nat.le_mul_of_pos_right r (by omega)
    omega
  have hrew : (-1 : ℤ⟦X⟧) ^ (M + r) * (PowerSeries.X : ℤ⟦X⟧) ^ kExp M r * inv1 (kProd M r) =
      (PowerSeries.X : ℤ⟦X⟧) ^ kExp M r * ((-1 : ℤ⟦X⟧) ^ (M + r) * inv1 (kProd M r)) := by ring
  rw [hrew]
  exact coeff_X_pow_mul_eq_zero he _

private def kRem (M : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun d ↦ ∑ r ∈ Finset.range (d + 1), PowerSeries.coeff d (kSummand M r)

private lemma hasSum_kSummand (M : ℕ) : HasSum (kSummand M) (kRem M) :=
  hasSum_mk_of_coeff_vanish (kSummand M) (fun d ↦ d + 1) (kSummand_vanish M)

private lemma k_telescoping_term (M s : ℕ) :
    kSummand M (s + 1) - kSummand (M + 1) s = kAux M s - kAux M (s + 1) := by
  unfold kSummand kAux
  have hinv_left : inv1 (kProd (M + 1) s) =
      (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (4 * M + 2)) * inv1 (kProd M (s + 1)) := by
    rw [kProd_succ_left M s]
    exact (mul_inv1_cancel_left (constantCoeff_one_sub_X_pow (by omega))
      (kProd_const (M + 1) s)).symm
  have hinv_right : inv1 (kProd M s) =
      (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (4 * (M + s + 1) + 2)) * inv1 (kProd M (s + 1)) := by
    rw [kProd_succ_right M s]
    exact (mul_inv1_cancel_right (kProd_const M s)
      (constantCoeff_one_sub_X_pow (by omega))).symm
  have hMs : M + (s + 1) = M + s + 1 := by omega
  have hM1s : M + 1 + s = M + s + 1 := by omega
  rw [hMs, hM1s, hinv_left, hinv_right]
  have hpow1 : (PowerSeries.X : ℤ⟦X⟧) ^ kExp (M + 1) s =
      (PowerSeries.X : ℤ⟦X⟧) ^ kExp M (s + 1) *
        (PowerSeries.X : ℤ⟦X⟧) ^ (4 * (M + s + 1) + 2) := by
    rw [kExp_succ_left M s, pow_add]
  have hpow2 : (PowerSeries.X : ℤ⟦X⟧) ^ kExp M (s + 1 + 1) =
      (PowerSeries.X : ℤ⟦X⟧) ^ kExp (M + 1) s *
        (PowerSeries.X : ℤ⟦X⟧) ^ (4 * M + 2) := by
    rw [show s + 1 + 1 = s + 2 by omega, ← kExp_add_first M s, pow_add]
  rw [hpow2, hpow1, pow_add (-1 : ℤ⟦X⟧) (M + s + 1) 1, pow_one]
  ring

private lemma kRem_sub_succ (M : ℕ) :
    kRem M - kRem (M + 1) =
      (-1 : ℤ⟦X⟧) ^ M *
        ((PowerSeries.X : ℤ⟦X⟧) ^ (6 * M ^ 2 + 4 * M) +
          (PowerSeries.X : ℤ⟦X⟧) ^ (6 * M ^ 2 + 8 * M + 2)) := by
  have haux_sum : HasSum (fun s ↦ kSummand M (s + 1) - kSummand (M + 1) s) (kAux M 0) := by
    refine hasSum_of_sub_eq_and_coeff_zero (kAux M) _
      (fun s ↦ (k_telescoping_term M s).symm) ?_
    intro d s hds
    unfold kAux
    have he : d < kExp M (s + 1) := by
      unfold kExp
      have h1 : s + 1 ≤ (s + 1) * (s + 1 + 1) := Nat.le_mul_of_pos_right (s + 1) (by omega)
      omega
    have hrew : (-1 : ℤ⟦X⟧) ^ (M + s + 1) * (PowerSeries.X : ℤ⟦X⟧) ^ kExp M (s + 1) *
        inv1 (kProd M s) =
        (PowerSeries.X : ℤ⟦X⟧) ^ kExp M (s + 1) *
          ((-1 : ℤ⟦X⟧) ^ (M + s + 1) * inv1 (kProd M s)) := by ring
    rw [hrew]
    exact coeff_X_pow_mul_eq_zero he _
  have hshift1 : HasSum (fun s ↦ kSummand M (s + 1)) (kRem M - kSummand M 0) := by
    have hM := hasSum_kSummand M
    rw [← hasSum_nat_add_iff' 1] at hM
    simpa [Finset.sum_range_one] using hM
  have heq := (hshift1.sub (hasSum_kSummand (M + 1))).unique haux_sum
  have h0 : kSummand M 0 + kAux M 0 =
      (-1 : ℤ⟦X⟧) ^ M *
        ((PowerSeries.X : ℤ⟦X⟧) ^ (6 * M ^ 2 + 4 * M) +
          (PowerSeries.X : ℤ⟦X⟧) ^ (6 * M ^ 2 + 8 * M + 2)) := by
    unfold kSummand kAux
    have hk0 : kProd M 0 = 1 - (PowerSeries.X : ℤ⟦X⟧) ^ (4 * M + 2) := by
      simp [kProd]
    have he0 : kExp M 0 = 6 * M ^ 2 + 4 * M := by unfold kExp; ring
    have he1 : kExp M 1 = (6 * M ^ 2 + 4 * M) + (4 * M + 2) + (4 * M + 2) := by unfold kExp; ring
    have he2 : 6 * M ^ 2 + 8 * M + 2 = (6 * M ^ 2 + 4 * M) + (4 * M + 2) := by ring
    have hc : PowerSeries.constantCoeff (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (4 * M + 2)) = 1 :=
      constantCoeff_one_sub_X_pow (by omega)
    rw [hk0, he0, he1, he2, Nat.add_zero, pow_add (-1 : ℤ⟦X⟧) M 1, pow_one,
      pow_add (PowerSeries.X : ℤ⟦X⟧) ((6 * M ^ 2 + 4 * M) + (4 * M + 2)) (4 * M + 2),
      pow_add (PowerSeries.X : ℤ⟦X⟧) (6 * M ^ 2 + 4 * M) (4 * M + 2)]
    calc
      (-1 : ℤ⟦X⟧) ^ M * (PowerSeries.X : ℤ⟦X⟧) ^ (6 * M ^ 2 + 4 * M) *
          inv1 (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (4 * M + 2)) +
        (-1 : ℤ⟦X⟧) ^ M * (-1) *
          ((PowerSeries.X : ℤ⟦X⟧) ^ (6 * M ^ 2 + 4 * M) *
            (PowerSeries.X : ℤ⟦X⟧) ^ (4 * M + 2) * (PowerSeries.X : ℤ⟦X⟧) ^ (4 * M + 2)) *
          inv1 (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (4 * M + 2))
          = (-1 : ℤ⟦X⟧) ^ M * (PowerSeries.X : ℤ⟦X⟧) ^ (6 * M ^ 2 + 4 * M) *
              (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (4 * M + 2)) *
              ((1 - (PowerSeries.X : ℤ⟦X⟧) ^ (4 * M + 2)) *
                inv1 (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (4 * M + 2))) := by ring
      _ = (-1 : ℤ⟦X⟧) ^ M *
            ((PowerSeries.X : ℤ⟦X⟧) ^ (6 * M ^ 2 + 4 * M) +
              (PowerSeries.X : ℤ⟦X⟧) ^ (6 * M ^ 2 + 4 * M) *
                (PowerSeries.X : ℤ⟦X⟧) ^ (4 * M + 2)) := by
            rw [mul_inv1 hc]
            ring
  calc
    kRem M - kRem (M + 1)
        = (kRem M - kSummand M 0 - kRem (M + 1)) + kSummand M 0 := by ring
    _ = kAux M 0 + kSummand M 0 := by rw [heq]
    _ = kSummand M 0 + kAux M 0 := by ring
    _ = (-1 : ℤ⟦X⟧) ^ M *
          ((PowerSeries.X : ℤ⟦X⟧) ^ (6 * M ^ 2 + 4 * M) +
            (PowerSeries.X : ℤ⟦X⟧) ^ (6 * M ^ 2 + 8 * M + 2)) := h0

private lemma kRem_coeff_zero {d M : ℕ} (hdM : d < M) :
    PowerSeries.coeff d (kRem M) = 0 := by
  rw [kRem, PowerSeries.coeff_mk]
  refine Finset.sum_eq_zero fun r _ ↦ ?_
  unfold kSummand
  have he : d < kExp M r := by
    unfold kExp
    omega
  have hrew : (-1 : ℤ⟦X⟧) ^ (M + r) * (PowerSeries.X : ℤ⟦X⟧) ^ kExp M r * inv1 (kProd M r) =
      (PowerSeries.X : ℤ⟦X⟧) ^ kExp M r * ((-1 : ℤ⟦X⟧) ^ (M + r) * inv1 (kProd M r)) := by ring
  rw [hrew]
  exact coeff_X_pow_mul_eq_zero he _

private lemma one_sub_X_mul_kRem_zero :
    1 - (PowerSeries.X : ℤ⟦X⟧) * kRem 0 = a186424FalseTheta := by
  have hk_tel : HasSum (fun M : ℕ ↦
      (-1 : ℤ⟦X⟧) ^ M *
        ((PowerSeries.X : ℤ⟦X⟧) ^ (6 * M ^ 2 + 4 * M) +
          (PowerSeries.X : ℤ⟦X⟧) ^ (6 * M ^ 2 + 8 * M + 2))) (kRem 0) :=
    hasSum_of_sub_eq_and_coeff_zero kRem _ kRem_sub_succ (fun d M h ↦ kRem_coeff_zero h)
  have hmul : HasSum (fun M : ℕ ↦
      (-1 : ℤ⟦X⟧) ^ (M + 1) *
        ((PowerSeries.X : ℤ⟦X⟧) ^ a186424 (2 * M) +
          (PowerSeries.X : ℤ⟦X⟧) ^ a186424 (2 * M + 1)))
      (-(PowerSeries.X : ℤ⟦X⟧) * kRem 0) := by
    refine (hk_tel.mul_left (-(PowerSeries.X : ℤ⟦X⟧))).congr_fun fun M ↦ ?_
    have hcl := a186424_closed_form.2 M
    rw [hcl.1, hcl.2, pow_add (-1 : ℤ⟦X⟧) M 1, pow_one,
      pow_add (PowerSeries.X : ℤ⟦X⟧) (6 * M ^ 2 + 4 * M) 1,
      pow_add (PowerSeries.X : ℤ⟦X⟧) (6 * M ^ 2 + 8 * M + 2) 1, pow_one]
    ring
  ext d
  have hcoeff := (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff (R := ℤ)).mp hmul d
  have hterm : ∀ M : ℕ,
      PowerSeries.coeff d
        ((-1 : ℤ⟦X⟧) ^ (M + 1) *
          ((PowerSeries.X : ℤ⟦X⟧) ^ a186424 (2 * M) +
            (PowerSeries.X : ℤ⟦X⟧) ^ a186424 (2 * M + 1))) =
      (-1 : ℤ) ^ (M + 1) *
        ((if d = a186424 (2 * M) then (1 : ℤ) else 0) +
          (if d = a186424 (2 * M + 1) then (1 : ℤ) else 0)) := by
    intro M
    rcases Nat.even_or_odd (M + 1) with h | h
    · rw [h.neg_one_pow, h.neg_one_pow, one_mul, one_mul, map_add,
        PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow]
    · rw [h.neg_one_pow, h.neg_one_pow, neg_one_mul, neg_one_mul, map_neg, map_add,
        PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow]
  simp_rw [hterm] at hcoeff
  rw [a186424FalseTheta, PowerSeries.coeff_mk, sub_eq_add_neg, map_add]
  have hneg_eq : (-(PowerSeries.X : ℤ⟦X⟧) * kRem 0) = -((PowerSeries.X : ℤ⟦X⟧) * kRem 0) := by ring
  rw [hneg_eq] at hcoeff
  by_cases hd0 : d = 0
  · subst hd0
    have hzero : HasSum (fun M : ℕ ↦
        (-1 : ℤ) ^ (M + 1) *
          ((if (0 : ℕ) = a186424 (2 * M) then (1 : ℤ) else 0) +
            (if (0 : ℕ) = a186424 (2 * M + 1) then (1 : ℤ) else 0))) (0 : ℤ) := by
      convert hasSum_zero (α := ℤ) (β := ℕ) with M
      have h1 : (0 : ℕ) ≠ a186424 (2 * M) := by have := a186424_pos (2 * M); omega
      have h2 : (0 : ℕ) ≠ a186424 (2 * M + 1) := by have := a186424_pos (2 * M + 1); omega
      simp [h1, h2]
    have hval := hcoeff.unique hzero
    simp [hval]
  · simp only [hd0, ↓reduceIte, PowerSeries.coeff_one, zero_add]
    split_ifs with hex
    · set m₀ := hex.choose
      have hm₀ : a186424 m₀ = d := hex.choose_spec
      set r₀ := m₀ / 2
      have hmono := a186424_closed_form.1
      have hinj := hmono.injective
      have hsingle : HasSum (fun M : ℕ ↦
          (-1 : ℤ) ^ (M + 1) *
            ((if d = a186424 (2 * M) then (1 : ℤ) else 0) +
              (if d = a186424 (2 * M + 1) then (1 : ℤ) else 0)))
          ((-1 : ℤ) ^ (r₀ + 1)) := by
        have hs := hasSum_ite_eq r₀ ((-1 : ℤ) ^ (r₀ + 1))
        refine hs.congr_fun fun M ↦ ?_
        by_cases hM : M = r₀
        · subst hM
          have hpar : m₀ = 2 * r₀ ∨ m₀ = 2 * r₀ + 1 := by omega
          rcases hpar with hev | hodd
          · have h1 : d = a186424 (2 * r₀) := by rw [← hm₀, hev]
            have h2 : d ≠ a186424 (2 * r₀ + 1) := by
              intro hc
              have := hinj (hm₀.trans hc)
              omega
            simp only [eq_true h1, eq_false h2, ↓reduceIte]
            ring
          · have h1 : d ≠ a186424 (2 * r₀) := by
              intro hc
              have := hinj (hm₀.trans hc)
              omega
            have h2 : d = a186424 (2 * r₀ + 1) := by rw [← hm₀, hodd]
            simp only [eq_false h1, eq_true h2, ↓reduceIte]
            ring
        · have h1 : d ≠ a186424 (2 * M) := by
            intro hc
            have := hinj (hm₀.trans hc)
            omega
          have h2 : d ≠ a186424 (2 * M + 1) := by
            intro hc
            have := hinj (hm₀.trans hc)
            omega
          simp [hM, h1, h2]
      exact hcoeff.unique hsingle
    · have hzero : HasSum (fun M : ℕ ↦
          (-1 : ℤ) ^ (M + 1) *
            ((if d = a186424 (2 * M) then (1 : ℤ) else 0) +
              (if d = a186424 (2 * M + 1) then (1 : ℤ) else 0))) (0 : ℤ) := by
        convert hasSum_zero (α := ℤ) (β := ℕ) with M
        have h1 : d ≠ a186424 (2 * M) := fun hc ↦ hex ⟨2 * M, hc.symm⟩
        have h2 : d ≠ a186424 (2 * M + 1) := fun hc ↦ hex ⟨2 * M + 1, hc.symm⟩
        simp [h1, h2]
      exact hcoeff.unique hzero

private lemma inv1_one_sub_X_mul_rfRem_zero :
    inv1 (1 - (PowerSeries.X : ℤ⟦X⟧)) * rfRem 0 = kRem 0 := by
  have hrf_tel : HasSum (fun m : ℕ ↦
      (-1 : ℤ⟦X⟧) ^ m * (PowerSeries.X : ℤ⟦X⟧) ^ (2 * m * (m + 1)) *
        inv1 (rfMinusProd m) * inv1 (rfPlusProd (m + 1))) (rfRem 0) :=
    hasSum_of_sub_eq_and_coeff_zero rfRem _ rfRem_sub_succ (fun d M h ↦ rfRem_coeff_zero h)
  have hc1 : PowerSeries.constantCoeff (1 - (PowerSeries.X : ℤ⟦X⟧)) = 1 := by
    have := constantCoeff_one_sub_X_pow (by omega : 0 < 1)
    rwa [pow_one] at this
  have hrhs := hrf_tel.mul_left (inv1 (1 - (PowerSeries.X : ℤ⟦X⟧)))
  have hrhs_eq : HasSum (kSummand 0) (inv1 (1 - (PowerSeries.X : ℤ⟦X⟧)) * rfRem 0) := by
    refine hrhs.congr_fun fun m ↦ ?_
    unfold kSummand
    have hexp : kExp 0 m = 2 * m * (m + 1) := by unfold kExp; ring
    have hinv : inv1 (1 - (PowerSeries.X : ℤ⟦X⟧)) * inv1 (rfMinusProd m) *
        inv1 (rfPlusProd (m + 1)) = inv1 (kProd 0 m) := by
      rw [← minus_plus_prod_eq_kProd m,
        inv1_mul_distrib (by rw [map_mul, hc1, rfMinusProd_const, mul_one]) (rfPlusProd_const _),
        inv1_mul_distrib hc1 (rfMinusProd_const m)]
    rw [hexp, Nat.zero_add]
    exact (calc
      inv1 (1 - (PowerSeries.X : ℤ⟦X⟧)) *
          ((-1 : ℤ⟦X⟧) ^ m * (PowerSeries.X : ℤ⟦X⟧) ^ (2 * m * (m + 1)) *
            inv1 (rfMinusProd m) * inv1 (rfPlusProd (m + 1)))
          = (-1 : ℤ⟦X⟧) ^ m * (PowerSeries.X : ℤ⟦X⟧) ^ (2 * m * (m + 1)) *
              (inv1 (1 - (PowerSeries.X : ℤ⟦X⟧)) * inv1 (rfMinusProd m) *
                inv1 (rfPlusProd (m + 1))) := by ring
      _ = (-1 : ℤ⟦X⟧) ^ m * (PowerSeries.X : ℤ⟦X⟧) ^ (2 * m * (m + 1)) *
            inv1 (kProd 0 m) := by rw [hinv]).symm
  exact hrhs_eq.unique (hasSum_kSummand 0)

/-- Bala's base false-theta identity (`OEIS A186424` `%F` lines 21–22) under
`PowerSeries.WithPiTopology` (discrete topology on `ℤ`). -/
theorem a186424_base_series :
    HasSum (fun n : ℕ ↦ (-1 : ℤ⟦X⟧) ^ n * PowerSeries.X ^ n *
      PowerSeries.invOfUnit
        (∏ k ∈ Finset.Icc 1 n, (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) (1 : ℤˣ))
      a186424FalseTheta := by
  have hc1 : PowerSeries.constantCoeff (1 - (PowerSeries.X : ℤ⟦X⟧)) = 1 := by
    have := constantCoeff_one_sub_X_pow (by omega : 0 < 1)
    rwa [pow_one] at this
  have htail : HasSum (fun m : ℕ ↦
      (-1 : ℤ⟦X⟧) ^ (m + 1) * (PowerSeries.X : ℤ⟦X⟧) ^ (m + 1) *
        inv1 (∏ k ∈ Finset.Icc 1 (m + 1), (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))))
      (-(PowerSeries.X : ℤ⟦X⟧) * kRem 0) := by
    have hmul := (hasSum_rfSummand 0).mul_left (-(PowerSeries.X : ℤ⟦X⟧) * inv1 (1 - PowerSeries.X))
    have hsum_val : -(PowerSeries.X : ℤ⟦X⟧) * inv1 (1 - PowerSeries.X) * rfRem 0 =
        -(PowerSeries.X : ℤ⟦X⟧) * kRem 0 := by
      rw [mul_assoc, inv1_one_sub_X_mul_rfRem_zero]
    rw [hsum_val] at hmul
    refine hmul.congr_fun fun m ↦ ?_
    unfold rfSummand
    have hexp0 : rfExp 0 m = m := by unfold rfExp; ring
    rw [hexp0, Nat.zero_add, rfPlusProd, Finset.prod_range_zero, inv1_one, mul_one]
    have hinv_minus : inv1 (1 - PowerSeries.X) * inv1 (rfMinusProd m) =
        inv1 (∏ k ∈ Finset.Icc 1 (m + 1), (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) := by
      rw [← one_sub_X_mul_rfMinusProd m, inv1_mul_distrib hc1 (rfMinusProd_const m)]
    rw [pow_add (-1 : ℤ⟦X⟧) m 1, pow_add (PowerSeries.X : ℤ⟦X⟧) m 1, pow_one, pow_one]
    exact (calc
      -(PowerSeries.X : ℤ⟦X⟧) * inv1 (1 - PowerSeries.X) *
          ((-1 : ℤ⟦X⟧) ^ m * (PowerSeries.X : ℤ⟦X⟧) ^ m * inv1 (rfMinusProd m))
          = (-1 : ℤ⟦X⟧) ^ m * (-1) * ((PowerSeries.X : ℤ⟦X⟧) ^ m * PowerSeries.X) *
              (inv1 (1 - PowerSeries.X) * inv1 (rfMinusProd m)) := by ring
      _ = (-1 : ℤ⟦X⟧) ^ m * (-1) * ((PowerSeries.X : ℤ⟦X⟧) ^ m * PowerSeries.X) *
            inv1 (∏ k ∈ Finset.Icc 1 (m + 1),
              (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) := by rw [hinv_minus]).symm
  have hfull := HasSum.zero_add (f := fun n : ℕ ↦ (-1 : ℤ⟦X⟧) ^ n * PowerSeries.X ^ n *
      inv1 (∏ k ∈ Finset.Icc 1 n, (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1)))) htail
  have h0 : (-1 : ℤ⟦X⟧) ^ 0 * (PowerSeries.X : ℤ⟦X⟧) ^ 0 *
      inv1 (∏ k ∈ Finset.Icc 1 0, (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) = 1 := by
    simp [inv1_one]
  rw [h0] at hfull
  have hval : (1 : ℤ⟦X⟧) + -(PowerSeries.X : ℤ⟦X⟧) * kRem 0 = a186424FalseTheta := by
    rw [← one_sub_X_mul_kRem_zero]
    ring
  rwa [hval] at hfull

/-! ### Section 5: Link 3 — Polynomial Family, Shift-and-Cancel Induction, and Uniqueness -/

/-- Closed-form product-and-sum formula for `a186424Poly N` (`∀ N : ℕ`). -/
theorem a186424Poly_closed_form (N : ℕ) :
    a186424Poly N =
      (∏ j ∈ Finset.Icc 1 N, (1 + (Polynomial.X : ℤ[X]) ^ (2 * j - 1))) -
        ∑ m ∈ Finset.Icc 1 N,
          (Polynomial.X : ℤ[X]) ^ m *
            ∏ j ∈ Finset.Icc (m + 1) N, (1 + (Polynomial.X : ℤ[X]) ^ (2 * j - 1)) := by
  induction N with
  | zero =>
    simp [a186424Poly]
  | succ N ih =>
    rw [a186424Poly, ih, finset_Icc_succ_right (by omega : 1 ≤ N + 1),
      Finset.prod_insert (by simp), Finset.sum_insert (by simp)]
    have htop_prod : ∏ j ∈ Finset.Icc (N + 1 + 1) (N + 1),
        (1 + (Polynomial.X : ℤ[X]) ^ (2 * j - 1)) = 1 := by
      rw [finset_Icc_of_gt (by omega), Finset.prod_empty]
    have hrest :
        ∑ m ∈ Finset.Icc 1 N,
          (Polynomial.X : ℤ[X]) ^ m *
            ∏ j ∈ Finset.Icc (m + 1) (N + 1), (1 + (Polynomial.X : ℤ[X]) ^ (2 * j - 1)) =
        (1 + (Polynomial.X : ℤ[X]) ^ (2 * N + 1)) *
          ∑ m ∈ Finset.Icc 1 N,
            (Polynomial.X : ℤ[X]) ^ m *
              ∏ j ∈ Finset.Icc (m + 1) N, (1 + (Polynomial.X : ℤ[X]) ^ (2 * j - 1)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm ↦ ?_
      rw [Finset.mem_Icc] at hm
      rw [finset_Icc_succ_right (by omega : m + 1 ≤ N + 1), Finset.prod_insert (by simp)]
      have hexp : 2 * (N + 1) - 1 = 2 * N + 1 := by omega
      rw [hexp]
      ring
    have hexp : 2 * (N + 1) - 1 = 2 * N + 1 := by omega
    rw [hexp, htop_prod, hrest]
    ring

/-- Adjudicated `N = 0` boundary and verbatim match to `OEIS A186424` empirical polynomials
for `N = 1..4`. -/
theorem a186424Poly_empirical_values :
    a186424Poly 0 = 1 ∧
      a186424Poly 1 = 1 ∧
      a186424Poly 2 = 1 - Polynomial.X ^ 2 + Polynomial.X ^ 3 ∧
      a186424Poly 3 =
        1 - Polynomial.X ^ 2 + Polynomial.X ^ 5 - Polynomial.X ^ 7 + Polynomial.X ^ 8 ∧
      a186424Poly 4 =
        1 - Polynomial.X ^ 2 - Polynomial.X ^ 4 + Polynomial.X ^ 5 + Polynomial.X ^ 8 -
          Polynomial.X ^ 9 + Polynomial.X ^ 12 - Polynomial.X ^ 14 + Polynomial.X ^ 15 := by
  have h0 : a186424Poly 0 = 1 := rfl
  have h1 : a186424Poly 1 = 1 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, a186424Poly, h0]
    ring
  have h2 : a186424Poly 2 = 1 - Polynomial.X ^ 2 + Polynomial.X ^ 3 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, a186424Poly, h1]
    ring
  have h3 : a186424Poly 3 =
      1 - Polynomial.X ^ 2 + Polynomial.X ^ 5 - Polynomial.X ^ 7 + Polynomial.X ^ 8 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, a186424Poly, h2]
    ring
  have h4 : a186424Poly 4 =
      1 - Polynomial.X ^ 2 - Polynomial.X ^ 4 + Polynomial.X ^ 5 + Polynomial.X ^ 8 -
        Polynomial.X ^ 9 + Polynomial.X ^ 12 - Polynomial.X ^ 14 + Polynomial.X ^ 15 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, a186424Poly, h3]
    ring
  exact ⟨h0, h1, h2, h3, h4⟩

private lemma deg_step_arith {M : ℕ} (hM : 1 ≤ M) :
    (2 * M + 1) + (M ^ 2 - 1) = (M + 1) ^ 2 - 1 := by
  have h1 : 1 ≤ M ^ 2 := by nlinarith
  have h2 : 1 ≤ (M + 1) ^ 2 := by nlinarith
  zify [h1, h2]
  ring

private lemma lt_deg_step_arith {M : ℕ} (hM : 1 ≤ M) :
    M + 1 < (M + 1) ^ 2 - 1 := by
  have h1 : 1 ≤ (M + 1) ^ 2 := by nlinarith
  zify [h1]
  nlinarith

/-- Exact degree, monicity, and constant term of `a186424Poly N`. -/
theorem a186424Poly_degree_and_monic :
    (a186424Poly 0).degree = (0 : WithBot ℕ) ∧
      (a186424Poly 0).Monic ∧
      ∀ N : ℕ, 1 ≤ N →
        (a186424Poly N).degree = ((N ^ 2 - 1 : ℕ) : WithBot ℕ) ∧
          (a186424Poly N).Monic ∧
          (a186424Poly N).coeff 0 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · change (1 : ℤ[X]).degree = (0 : WithBot ℕ)
    exact Polynomial.degree_one
  · change (1 : ℤ[X]).Monic
    exact Polynomial.monic_one
  · intro N hN
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
    clear hN
    induction k with
    | zero =>
      have h1 : a186424Poly 1 = 1 := a186424Poly_empirical_values.2.1
      rw [show (0 + 1 : ℕ) = 1 from rfl, h1]
      refine ⟨Polynomial.degree_one, Polynomial.monic_one, ?_⟩
      simp
    | succ k ih =>
      set M := k + 1
      have hM : 1 ≤ M := by omega
      rcases ih with ⟨hdeg, hmonic, hcoeff0⟩
      rw [show k + 1 + 1 = M + 1 by omega, a186424Poly]
      set fac : ℤ[X] := Polynomial.X ^ (2 * M + 1) + Polynomial.C (1 : ℤ)
      have hfac_eq : (1 + Polynomial.X ^ (2 * M + 1) : ℤ[X]) = fac := by
        simp [fac, add_comm]
      have hfac_monic : fac.Monic := Polynomial.monic_X_pow_add_C 1 (by omega)
      have hfac_deg : fac.degree = ((2 * M + 1 : ℕ) : WithBot ℕ) := by
        change (Polynomial.X ^ (2 * M + 1) + Polynomial.C (1 : ℤ)).degree =
          ((2 * M + 1 : ℕ) : WithBot ℕ)
        rw [Polynomial.degree_X_pow_add_C (by omega : 0 < 2 * M + 1) (1 : ℤ)]
      rw [hfac_eq, sub_eq_add_neg]
      have htop_monic : (fac * a186424Poly M).Monic := hfac_monic.mul hmonic
      have htop_deg : (fac * a186424Poly M).degree = (((M + 1) ^ 2 - 1 : ℕ) : WithBot ℕ) := by
        rw [hmonic.degree_mul, hfac_deg, hdeg, ← Nat.cast_add, deg_step_arith hM]
      have hlow_lt : (-(Polynomial.X : ℤ[X]) ^ (M + 1)).degree < (fac * a186424Poly M).degree := by
        rw [Polynomial.degree_neg, Polynomial.degree_X_pow, htop_deg, Nat.cast_lt]
        exact lt_deg_step_arith hM
      refine ⟨(Polynomial.degree_add_eq_left_of_degree_lt hlow_lt).trans htop_deg,
        htop_monic.add_of_left hlow_lt, ?_⟩
      rw [Polynomial.coeff_add, Polynomial.coeff_neg, Polynomial.coeff_X_pow,
        Polynomial.mul_coeff_zero, hcoeff0]
      have hfac0 : fac.coeff 0 = 1 := by
        simp [fac, Polynomial.coeff_X_pow]
      simp [hfac0]

private def a186424MinusProd (m : ℕ) : ℤ⟦X⟧ :=
  ∏ k ∈ Finset.Icc 1 (m + 1), (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))

private def a186424PlusProd (N : ℕ) : ℤ⟦X⟧ :=
  ∏ j ∈ Finset.Icc 1 N, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * j - 1))

private lemma a186424MinusProd_const (m : ℕ) :
    PowerSeries.constantCoeff (a186424MinusProd m) = 1 := by
  refine constantCoeff_prod_one_sub _ _ fun k hk ↦ ?_
  rw [Finset.mem_Icc] at hk
  omega

private lemma a186424PlusProd_const (N : ℕ) :
    PowerSeries.constantCoeff (a186424PlusProd N) = 1 := by
  refine constantCoeff_prod_one_add _ _ fun j hj ↦ ?_
  rw [Finset.mem_Icc] at hj
  omega

private def a186424Summand (N m : ℕ) : ℤ⟦X⟧ :=
  (-1 : ℤ⟦X⟧) ^ (m + 1) * (PowerSeries.X : ℤ⟦X⟧) ^ ((2 * N + 1) * (m + 1) - N) *
    inv1 (a186424MinusProd m)

private lemma a186424Summand_vanish (N d m : ℕ) (hm : d + 1 ≤ m) :
    PowerSeries.coeff d (a186424Summand N m) = 0 := by
  unfold a186424Summand
  have hexp : d < (2 * N + 1) * (m + 1) - N := by
    have : (2 * N + 1) * (m + 1) = (2 * N * m + N + m + 1) + N := by ring
    omega
  have hrew : (-1 : ℤ⟦X⟧) ^ (m + 1) * (PowerSeries.X : ℤ⟦X⟧) ^ ((2 * N + 1) * (m + 1) - N) *
      inv1 (a186424MinusProd m) =
      (PowerSeries.X : ℤ⟦X⟧) ^ ((2 * N + 1) * (m + 1) - N) *
        ((-1 : ℤ⟦X⟧) ^ (m + 1) * inv1 (a186424MinusProd m)) := by ring
  rw [hrew]
  exact coeff_X_pow_mul_eq_zero hexp _

private def a186424Tail (N : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun d ↦ ∑ m ∈ Finset.range (d + 1), PowerSeries.coeff d (a186424Summand N m)

private lemma hasSum_a186424Summand (N : ℕ) : HasSum (a186424Summand N) (a186424Tail N) :=
  hasSum_mk_of_coeff_vanish (a186424Summand N) (fun d ↦ d + 1) (a186424Summand_vanish N)

private lemma a186424_shift_cancel (N : ℕ) :
    (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N + 1)) * a186424Tail N =
      -((PowerSeries.X : ℤ⟦X⟧) ^ (N + 1)) + a186424Tail (N + 1) := by
  have hdiff_sum := (hasSum_a186424Summand N).sub (hasSum_a186424Summand (N + 1))
  have hterm0 : a186424Summand N 0 - a186424Summand (N + 1) 0 =
      -((PowerSeries.X : ℤ⟦X⟧) ^ (N + 1)) := by
    unfold a186424Summand a186424MinusProd
    have hIcc1 : Finset.Icc 1 1 = {1} := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_singleton]
      omega
    have he1 : (2 * N + 1) * 1 - N = N + 1 := by omega
    have he2 : (2 * (N + 1) + 1) * 1 - (N + 1) = (N + 1) + 1 := by omega
    rw [Nat.zero_add, hIcc1, Finset.prod_singleton, he1, he2]
    have hpow1 : (PowerSeries.X : ℤ⟦X⟧) ^ (2 * 1 - 1) = PowerSeries.X := by simp
    rw [hpow1, pow_one (-1 : ℤ⟦X⟧), pow_add (PowerSeries.X : ℤ⟦X⟧) (N + 1) 1, pow_one]
    have hc1 : PowerSeries.constantCoeff (1 - (PowerSeries.X : ℤ⟦X⟧)) = 1 := by
      have := constantCoeff_one_sub_X_pow (by omega : 0 < 1)
      rwa [pow_one] at this
    calc
      (-1 : ℤ⟦X⟧) * (PowerSeries.X : ℤ⟦X⟧) ^ (N + 1) * inv1 (1 - PowerSeries.X) -
        (-1 : ℤ⟦X⟧) * ((PowerSeries.X : ℤ⟦X⟧) ^ (N + 1) * PowerSeries.X) *
          inv1 (1 - PowerSeries.X)
          = -((PowerSeries.X : ℤ⟦X⟧) ^ (N + 1) *
              ((1 - PowerSeries.X) * inv1 (1 - PowerSeries.X))) := by ring
      _ = -((PowerSeries.X : ℤ⟦X⟧) ^ (N + 1)) := by
            rw [mul_inv1 hc1, mul_one]
  have hterm_succ : ∀ r : ℕ,
      a186424Summand N (r + 1) - a186424Summand (N + 1) (r + 1) =
        -((PowerSeries.X : ℤ⟦X⟧) ^ (2 * N + 1) * a186424Summand N r) := by
    intro r
    unfold a186424Summand
    have hminus_split : a186424MinusProd (r + 1) =
        a186424MinusProd r * (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * r + 3)) := by
      unfold a186424MinusProd
      rw [finset_Icc_succ_right (by omega : 1 ≤ r + 1 + 1), Finset.prod_insert (by simp)]
      have : 2 * (r + 1 + 1) - 1 = 2 * r + 3 := by omega
      rw [this, mul_comm]
    have hcancel : (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * r + 3)) * inv1 (a186424MinusProd (r + 1)) =
        inv1 (a186424MinusProd r) := by
      rw [hminus_split]
      exact mul_inv1_cancel_right (a186424MinusProd_const r)
        (constantCoeff_one_sub_X_pow (by omega))
    have he1 : (2 * N + 1) * (r + 1 + 1) - N =
        (2 * N + 1) + ((2 * N + 1) * (r + 1) - N) := by
      have hsub : N ≤ (2 * N + 1) * (r + 1) := by nlinarith
      have : (2 * N + 1) * (r + 1 + 1) = (2 * N + 1) + (2 * N + 1) * (r + 1) := by ring
      omega
    have he2 : (2 * (N + 1) + 1) * (r + 1 + 1) - (N + 1) =
        ((2 * N + 1) + ((2 * N + 1) * (r + 1) - N)) + (2 * r + 3) := by
      have hsub : N ≤ (2 * N + 1) * (r + 1) := by nlinarith
      have : (2 * (N + 1) + 1) * (r + 1 + 1) =
          (2 * N + 1) * (r + 1) + (2 * N + 1) + (2 * r + 4) := by ring
      omega
    rw [he1, he2, pow_add (-1 : ℤ⟦X⟧) (r + 1) 1, pow_one,
      pow_add (PowerSeries.X : ℤ⟦X⟧) _ (2 * r + 3),
      pow_add (PowerSeries.X : ℤ⟦X⟧) (2 * N + 1) _]
    calc
      ((-1 : ℤ⟦X⟧) ^ (r + 1) * (-1)) *
          ((PowerSeries.X : ℤ⟦X⟧) ^ (2 * N + 1) *
            (PowerSeries.X : ℤ⟦X⟧) ^ ((2 * N + 1) * (r + 1) - N)) *
          inv1 (a186424MinusProd (r + 1)) -
        ((-1 : ℤ⟦X⟧) ^ (r + 1) * (-1)) *
          ((PowerSeries.X : ℤ⟦X⟧) ^ (2 * N + 1) *
            (PowerSeries.X : ℤ⟦X⟧) ^ ((2 * N + 1) * (r + 1) - N) *
            (PowerSeries.X : ℤ⟦X⟧) ^ (2 * r + 3)) *
          inv1 (a186424MinusProd (r + 1))
          = -((PowerSeries.X : ℤ⟦X⟧) ^ (2 * N + 1) * (-1 : ℤ⟦X⟧) ^ (r + 1) *
              (PowerSeries.X : ℤ⟦X⟧) ^ ((2 * N + 1) * (r + 1) - N) *
              ((1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * r + 3)) *
                inv1 (a186424MinusProd (r + 1)))) := by ring
      _ = -((PowerSeries.X : ℤ⟦X⟧) ^ (2 * N + 1) *
            ((-1 : ℤ⟦X⟧) ^ (r + 1) *
              (PowerSeries.X : ℤ⟦X⟧) ^ ((2 * N + 1) * (r + 1) - N) *
              inv1 (a186424MinusProd r))) := by
            rw [hcancel]
            ring
  have hshift_rhs : HasSum (fun m ↦ a186424Summand N m - a186424Summand (N + 1) m)
      (-((PowerSeries.X : ℤ⟦X⟧) ^ (N + 1)) -
        (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N + 1) * a186424Tail N) := by
    have h1 := ((hasSum_a186424Summand N).mul_left ((PowerSeries.X : ℤ⟦X⟧) ^ (2 * N + 1))).neg
    have h2 : HasSum (fun r ↦ a186424Summand N (r + 1) - a186424Summand (N + 1) (r + 1))
        (-((PowerSeries.X : ℤ⟦X⟧) ^ (2 * N + 1) * a186424Tail N)) :=
      h1.congr_fun fun r ↦ hterm_succ r
    have h3 := HasSum.zero_add (f := fun m ↦ a186424Summand N m - a186424Summand (N + 1) m) h2
    rwa [hterm0, ← sub_eq_add_neg] at h3
  have heq := hdiff_sum.unique hshift_rhs
  calc
    (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N + 1)) * a186424Tail N
        = (a186424Tail N - a186424Tail (N + 1)) + a186424Tail (N + 1) +
            (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N + 1) * a186424Tail N := by ring
    _ = (-((PowerSeries.X : ℤ⟦X⟧) ^ (N + 1)) -
          (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N + 1) * a186424Tail N) + a186424Tail (N + 1) +
          (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N + 1) * a186424Tail N := by rw [heq]
    _ = -((PowerSeries.X : ℤ⟦X⟧) ^ (N + 1)) + a186424Tail (N + 1) := by ring

private lemma plusProd_mul_a186424FalseTheta (N : ℕ) :
    a186424PlusProd N * a186424FalseTheta =
      Polynomial.toPowerSeries (a186424Poly N) + a186424Tail N := by
  induction N with
  | zero =>
    have hplus0 : a186424PlusProd 0 = 1 := by simp [a186424PlusProd]
    have hbase := a186424_base_series
    rw [← hasSum_nat_add_iff' 1] at hbase
    have h0 : (-1 : ℤ⟦X⟧) ^ 0 * (PowerSeries.X : ℤ⟦X⟧) ^ 0 *
        inv1 (∏ k ∈ Finset.Icc 1 0, (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) = 1 := by
      simp [inv1_one]
    rw [Finset.sum_range_one, h0] at hbase
    have hfun : (fun m : ℕ ↦ (-1 : ℤ⟦X⟧) ^ (m + 1) * (PowerSeries.X : ℤ⟦X⟧) ^ (m + 1) *
        inv1 (∏ k ∈ Finset.Icc 1 (m + 1), (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1)))) =
        a186424Summand 0 := by
      funext m
      unfold a186424Summand a186424MinusProd
      simp
    rw [hfun] at hbase
    have htail0 : a186424Tail 0 = a186424FalseTheta - 1 :=
      (hasSum_a186424Summand 0).unique hbase
    rw [hplus0, one_mul, htail0]
    change a186424FalseTheta = ((1 : ℤ[X]) : ℤ⟦X⟧) + (a186424FalseTheta - 1)
    push_cast
    ring
  | succ N ih =>
    have hplus_step : a186424PlusProd (N + 1) =
        (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N + 1)) * a186424PlusProd N := by
      unfold a186424PlusProd
      rw [finset_Icc_succ_right (by omega : 1 ≤ N + 1), Finset.prod_insert (by simp)]
      have hexp : 2 * (N + 1) - 1 = 2 * N + 1 := by omega
      rw [hexp]
    have hpoly_step : Polynomial.toPowerSeries (a186424Poly (N + 1)) =
        (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N + 1)) * Polynomial.toPowerSeries (a186424Poly N) -
          (PowerSeries.X : ℤ⟦X⟧) ^ (N + 1) := by
      rw [a186424Poly]
      push_cast
      rfl
    have hshift := a186424_shift_cancel N
    calc
      a186424PlusProd (N + 1) * a186424FalseTheta
          = (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N + 1)) *
              (a186424PlusProd N * a186424FalseTheta) := by rw [hplus_step, mul_assoc]
      _ = (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N + 1)) * Polynomial.toPowerSeries (a186424Poly N) +
            (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N + 1)) * a186424Tail N := by rw [ih, mul_add]
      _ = (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N + 1)) * Polynomial.toPowerSeries (a186424Poly N) +
            (-((PowerSeries.X : ℤ⟦X⟧) ^ (N + 1)) + a186424Tail (N + 1)) := by rw [hshift]
      _ = Polynomial.toPowerSeries (a186424Poly (N + 1)) + a186424Tail (N + 1) := by
            rw [hpoly_step]
            ring

/-- Explicit `N ≥ 0` family identity with `P(N, X) = a186424Poly N`. -/
theorem a186424_family_explicit (N : ℕ) :
    ∃ S : ℤ⟦X⟧,
      HasSum (fun m : ℕ ↦ (-1 : ℤ⟦X⟧) ^ (m + 1) *
        PowerSeries.X ^ ((2 * N + 1) * (m + 1) - N) *
        PowerSeries.invOfUnit
          (∏ k ∈ Finset.Icc 1 (m + 1), (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) (1 : ℤˣ)) S ∧
      PowerSeries.invOfUnit
        (∏ j ∈ Finset.Icc 1 N, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * j - 1))) (1 : ℤˣ) *
        (Polynomial.toPowerSeries (a186424Poly N) + S) = a186424FalseTheta := by
  refine ⟨a186424Tail N, hasSum_a186424Summand N, ?_⟩
  have hmul := plusProd_mul_a186424FalseTheta N
  calc
    inv1 (a186424PlusProd N) * (Polynomial.toPowerSeries (a186424Poly N) + a186424Tail N)
        = inv1 (a186424PlusProd N) * (a186424PlusProd N * a186424FalseTheta) := by rw [hmul]
    _ = (inv1 (a186424PlusProd N) * a186424PlusProd N) * a186424FalseTheta := by ring
    _ = a186424FalseTheta := by rw [inv1_mul (a186424PlusProd_const N), one_mul]

/-- Unique-polynomial existential form (`∃! P : ℤ[X], ...`) of Peter Bala's `A186424` family
(`∀ N : ℕ`). -/
theorem a186424_family (N : ℕ) :
    ∃! P : ℤ[X],
      ((N = 0 → P = 1) ∧ (1 ≤ N → P.degree = ((N ^ 2 - 1 : ℕ) : WithBot ℕ))) ∧
      ∃ S : ℤ⟦X⟧,
        HasSum (fun m : ℕ ↦ (-1 : ℤ⟦X⟧) ^ (m + 1) *
          PowerSeries.X ^ ((2 * N + 1) * (m + 1) - N) *
          PowerSeries.invOfUnit
            (∏ k ∈ Finset.Icc 1 (m + 1), (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) (1 : ℤˣ)) S ∧
        PowerSeries.invOfUnit
          (∏ j ∈ Finset.Icc 1 N, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * j - 1))) (1 : ℤˣ) *
          (Polynomial.toPowerSeries P + S) = a186424FalseTheta := by
  refine ⟨a186424Poly N, ⟨⟨?_, ?_⟩, a186424_family_explicit N⟩, ?_⟩
  · rintro rfl
    rfl
  · intro hN
    exact (a186424Poly_degree_and_monic.2.2 N hN).1
  · rintro Q ⟨_, S', hS'_sum, hQ_eq⟩
    have hS'_eq : S' = a186424Tail N := hS'_sum.unique (hasSum_a186424Summand N)
    rw [hS'_eq] at hQ_eq
    have hlhs : a186424PlusProd N * a186424FalseTheta =
        Polynomial.toPowerSeries Q + a186424Tail N := by
      calc
        a186424PlusProd N * a186424FalseTheta
            = a186424PlusProd N * (inv1 (a186424PlusProd N) *
                (Polynomial.toPowerSeries Q + a186424Tail N)) := by rw [← hQ_eq]; rfl
        _ = (a186424PlusProd N * inv1 (a186424PlusProd N)) *
              (Polynomial.toPowerSeries Q + a186424Tail N) := by ring
        _ = Polynomial.toPowerSeries Q + a186424Tail N := by
              rw [mul_inv1 (a186424PlusProd_const N), one_mul]
    have hrhs := plusProd_mul_a186424FalseTheta N
    have hpoly_ps : Polynomial.toPowerSeries Q = Polynomial.toPowerSeries (a186424Poly N) :=
      add_right_cancel (hlhs.symm.trans hrhs)
    exact Polynomial.coe_inj.mp hpoly_ps

/-- Immediate existential corollary (`∃ P : ℤ[X], ...`) of `a186424_family`. -/
theorem a186424_family_exists (N : ℕ) :
    ∃ P : ℤ[X],
      ((N = 0 → P = 1) ∧ (1 ≤ N → P.degree = ((N ^ 2 - 1 : ℕ) : WithBot ℕ))) ∧
      ∃ S : ℤ⟦X⟧,
        HasSum (fun m : ℕ ↦ (-1 : ℤ⟦X⟧) ^ (m + 1) *
          PowerSeries.X ^ ((2 * N + 1) * (m + 1) - N) *
          PowerSeries.invOfUnit
            (∏ k ∈ Finset.Icc 1 (m + 1), (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) (1 : ℤˣ)) S ∧
        PowerSeries.invOfUnit
          (∏ j ∈ Finset.Icc 1 N, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * j - 1))) (1 : ℤˣ) *
          (Polynomial.toPowerSeries P + S) = a186424FalseTheta :=
  (a186424_family N).exists

/-! ### Section 6: Boundary Calibration, `N = 0` Slip Refutation, and Coefficient Breakdown -/

/-- Explicit `Q_5(X)` (all coefficients still in `{-1, 0, +1}`) and `Q_6(X)` with its first
coefficient outside `{-1, 0, +1}`, namely `[X^13] Q_6(X) = -2`. -/
theorem a186424Poly_five_and_six :
    a186424Poly 5 =
      1 - Polynomial.X ^ 2 - Polynomial.X ^ 4 + Polynomial.X ^ 8 - Polynomial.X ^ 11 +
        Polynomial.X ^ 12 - Polynomial.X ^ 13 + Polynomial.X ^ 15 + Polynomial.X ^ 17 -
        Polynomial.X ^ 18 + Polynomial.X ^ 21 - Polynomial.X ^ 23 + Polynomial.X ^ 24 ∧
    a186424Poly 6 =
      1 - Polynomial.X ^ 2 - Polynomial.X ^ 4 - Polynomial.X ^ 6 + Polynomial.X ^ 8 +
        Polynomial.X ^ 12 - 2 * Polynomial.X ^ 13 + Polynomial.X ^ 17 - Polynomial.X ^ 18 +
        Polynomial.X ^ 19 + Polynomial.X ^ 21 - Polynomial.X ^ 22 + Polynomial.X ^ 26 +
        Polynomial.X ^ 28 - Polynomial.X ^ 29 + Polynomial.X ^ 32 - Polynomial.X ^ 34 +
        Polynomial.X ^ 35 ∧
    (a186424Poly 6).coeff 13 = -2 := by
  have h5 : a186424Poly 5 =
      1 - Polynomial.X ^ 2 - Polynomial.X ^ 4 + Polynomial.X ^ 8 - Polynomial.X ^ 11 +
        Polynomial.X ^ 12 - Polynomial.X ^ 13 + Polynomial.X ^ 15 + Polynomial.X ^ 17 -
        Polynomial.X ^ 18 + Polynomial.X ^ 21 - Polynomial.X ^ 23 + Polynomial.X ^ 24 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, a186424Poly, a186424Poly_empirical_values.2.2.2.2]
    ring
  have h6 : a186424Poly 6 =
      1 - Polynomial.X ^ 2 - Polynomial.X ^ 4 - Polynomial.X ^ 6 + Polynomial.X ^ 8 +
        Polynomial.X ^ 12 - 2 * Polynomial.X ^ 13 + Polynomial.X ^ 17 - Polynomial.X ^ 18 +
        Polynomial.X ^ 19 + Polynomial.X ^ 21 - Polynomial.X ^ 22 + Polynomial.X ^ 26 +
        Polynomial.X ^ 28 - Polynomial.X ^ 29 + Polynomial.X ^ 32 - Polynomial.X ^ 34 +
        Polynomial.X ^ 35 := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, a186424Poly, h5]
    ring
  refine ⟨h5, h6, ?_⟩
  rw [h6]
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_one]

/-- Formal verification of Peter Bala's `N = 0` constant-term slip: substituting literal
`P(0, X) = 0` into the `N = 0` family identity produces constant term `0 ≠ 1` and therefore
fails `= a186424FalseTheta`. -/
theorem a186424_n0_zero_poly_fails :
    PowerSeries.invOfUnit
        (∏ j ∈ Finset.Icc 1 0, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * j - 1))) (1 : ℤˣ) *
        (Polynomial.toPowerSeries (0 : ℤ[X]) + a186424Tail 0) ≠
      a186424FalseTheta := by
  intro h
  have hplus0 : a186424PlusProd 0 = 1 := by simp [a186424PlusProd]
  have h0 := plusProd_mul_a186424FalseTheta 0
  rw [hplus0, one_mul] at h0
  have hzero : Polynomial.toPowerSeries (0 : ℤ[X]) = 0 := Polynomial.coe_zero
  have hone : Polynomial.toPowerSeries (a186424Poly 0) = 1 := Polynomial.coe_one
  have hprod0 : PowerSeries.invOfUnit
      (∏ j ∈ Finset.Icc 1 0, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * j - 1))) (1 : ℤˣ) = 1 := by
    simp [inv1_one]
  rw [hprod0, one_mul, hzero, zero_add] at h
  rw [hone] at h0
  have h1 : (0 : ℤ⟦X⟧) = 1 := by
    have := h.trans h0
    linear_combination this
  have hc := congrArg PowerSeries.constantCoeff h1
  simp at hc

/-- Spot verification of the first 20 terms (`a(0)..a(19)`) of `OEIS A186424`. -/
theorem a186424_oeis_spot_20 :
    (List.range 20).map a186424 =
      [1, 3, 11, 17, 33, 43, 67, 81, 113, 131, 171, 193, 241, 267, 323, 353, 417, 451, 523, 561] := by
  have he : ∀ r, a186424 (2 * r) = 6 * r ^ 2 + 4 * r + 1 := fun r ↦ (a186424_closed_form.2 r).1
  have ho : ∀ r, a186424 (2 * r + 1) = 6 * r ^ 2 + 8 * r + 3 := fun r ↦ (a186424_closed_form.2 r).2
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append]
  have h0 : a186424 0 = 1 := by simpa using he 0
  have h1 : a186424 1 = 3 := by simpa using ho 0
  have h2 : a186424 2 = 11 := by simpa using he 1
  have h3 : a186424 3 = 17 := by simpa using ho 1
  have h4 : a186424 4 = 33 := by simpa using he 2
  have h5 : a186424 5 = 43 := by simpa using ho 2
  have h6 : a186424 6 = 67 := by simpa using he 3
  have h7 : a186424 7 = 81 := by simpa using ho 3
  have h8 : a186424 8 = 113 := by simpa using he 4
  have h9 : a186424 9 = 131 := by simpa using ho 4
  have h10 : a186424 10 = 171 := by simpa using he 5
  have h11 : a186424 11 = 193 := by simpa using ho 5
  have h12 : a186424 12 = 241 := by simpa using he 6
  have h13 : a186424 13 = 267 := by simpa using ho 6
  have h14 : a186424 14 = 323 := by simpa using he 7
  have h15 : a186424 15 = 353 := by simpa using ho 7
  have h16 : a186424 16 = 417 := by simpa using he 8
  have h17 : a186424 17 = 451 := by simpa using ho 8
  have h18 : a186424 18 = 523 := by simpa using he 9
  have h19 : a186424 19 = 561 := by simpa using ho 9
  simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]

end

end Mathproofs.A186424
