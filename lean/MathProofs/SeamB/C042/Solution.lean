import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Seam B Entry C042 (OEIS A191579): Row Sums and First Three Columns

Proves the four-claim bundle from OEIS `A191579` (`%C` line 11) plus well-definedness
(`a191579_row_exists_unique`) against the frozen contract `PIN-C042.md` v1
(`sha256: 2c68f4c0ab89c832ab06bc973758ff53434148b319516b8ee33a745d2f31c2e4`,
`Statement.lean sha256: 5ee8b6f0acfb217cf7ee550361c575c5fc53429dc47357717b41b4b89a3fd239`).

Proof structure:
1. Eliminate odd rows of `a192062` to show `(a192062 (2 * n + 2) j : ℤ) = (uPoly n).eval (j + 2)`,
   where `uPoly n ∈ ℤ[X]` is the monic rescaled Chebyshev polynomial of the second kind
   (`u₀ = 1`, `u₁ = X`, `u_{n+2} = X * u_{n+1} - u_n`).
2. Prove `uPoly n` is monic of exact degree `n`, yielding row uniqueness via
   `Polynomial.eq_zero_of_infinite_isRoot` and descending coefficient extraction.
3. Combinatorial last-visit-to-height-0 decompositions on peakless nonnegative Motzkin words:
   - Excursion decomposition gives the generalized Catalan recurrence for `a004148`, hence
     `G_nat + X^2 * G_nat = 1 + X * G_nat + X^2 * G_nat^2` in `PowerSeries ℕ` where
     `G_nat = PowerSeries.mk a004148`.
   - Prefix decomposition at the last height-0 visit gives
     `a097724 n k = PowerSeries.coeff n (X^k * G_nat^(k+1))` for all `n, k : ℕ`,
     and height partitioning gives `a091964 n = ∑ k ∈ range (n + 1), a097724 n k`.
4. Square-root-free, substitution-free identity in `PowerSeries (Polynomial ℤ)`:
   factor `1 - C X * Z * G + Z^2 * G^2 = (1 - C (X + 1) * Z + Z^2) * G`, cancel units `G` and
   `1 - C (X + 1) * Z + Z^2` via `PowerSeries.isUnit_iff_constantCoeff`, and evaluate at `j + 2`
   to prove `IsA191579Row n (a097724 n)`, hence `a191579 n k = a097724 n k = [z^n](z^k G_nat^(k+1))`.
5. Deduce all five pinned theorems (`a191579_row_exists_unique`, `a191579_rowSum_eq_a091964`,
   `a191579_col0_eq_a004148`, `a191579_col1_eq_a089735`, `a191579_col2_eq_a098075`).
-/

open scoped BigOperators

namespace MathProofs.SeamB.C042

/-! ### 1. Auxiliary Sequence 1: Square Array `A192062` (`S`) -/

/-- OEIS A192062 (`S(m, j)`): square array defined columnwise by
`S(0, j) = 0`, `S(1, j) = 1`, `S(2i, j) = S(2i-2, j) + S(2i-1, j)` (`i ≥ 1`),
and `S(2i+1, j) = S(2i-1, j) + j * S(2i, j)` (`i ≥ 1`). -/
def a192062 : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, _ => 1
  | m + 2, j =>
    if (m + 2) % 2 = 0 then
      a192062 m j + a192062 (m + 1) j
    else
      a192062 m j + j * a192062 (m + 1) j

/-! ### 2. Primary Target Triangle: `A191579` (`R`) and Projections -/

/-- Connection-coefficient specification for the 0-indexed `n`-th row of `A191579`,
zero-extended for `k > n`, satisfying `S(2n+2, j+1) = ∑_{k=0..n} r(k) * S(2k+2, j)`
for every `j : ℕ` (corresponding to `j_orig = j + 1 ≥ 1` in `A191579` `%F`). -/
def IsA191579Row (n : ℕ) (r : ℕ → ℕ) : Prop :=
  (∀ k : ℕ, n < k → r k = 0) ∧
  ∀ j : ℕ, a192062 (2 * n + 2) (j + 1) =
    ∑ k ∈ Finset.range (n + 1), r k * a192062 (2 * k + 2) j

/-- OEIS A191579 (`R(n, k)`), 0-indexed (`0 ≤ k ≤ n`, zero-extended for `k > n`). -/
noncomputable def a191579 (n k : ℕ) : ℕ :=
  Classical.epsilon (IsA191579Row n) k

/-- Row-sum projection `∑_{k=0..n} R(n, k)` of `A191579`. -/
noncomputable def a191579RowSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), a191579 n k

/-- Column projection `n ↦ R(n, k)` of `A191579` (`k = 0, 1, 2, ...`). -/
noncomputable def a191579Col (k n : ℕ) : ℕ :=
  a191579 n k

/-! ### 3. Auxiliary Sequences 2–6: Peakless Motzkin Paths & Convolutions -/

/-- Step alphabet for Motzkin lattice paths: up `(1, 1)`, level `(1, 0)`, down `(1, -1)`. -/
inductive MotzkinStep : Type
  | U
  | H
  | D
  deriving DecidableEq

/-- Vertical step displacement in `ℤ`. -/
def MotzkinStep.delta : MotzkinStep → ℤ
  | .U => 1
  | .H => 0
  | .D => -1

/-- A Motzkin word is peakless if no `U` step is immediately followed by a `D` step. -/
def IsPeakless : List MotzkinStep → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => (x = .U → y ≠ .D) ∧ IsPeakless (y :: xs)

/-- Height after the first `i` steps of `w` (`prefixHeight w 0 = 0`). -/
def prefixHeight (w : List MotzkinStep) (i : ℕ) : ℤ :=
  ((w.take i).map MotzkinStep.delta).sum

/-- A peakless nonnegative Motzkin prefix (left factor of a peakless Motzkin path):
never goes below the x-axis (`0 ≤ prefixHeight w i` for all `i ≤ w.length`) and has no `UD` peak. -/
def IsPeaklessPrefix (w : List MotzkinStep) : Prop :=
  (∀ i : ℕ, i ≤ w.length → 0 ≤ prefixHeight w i) ∧ IsPeakless w

/-- Auxiliary Sequence 2 — OEIS A091964: number of left factors (prefixes) of peakless
Motzkin paths of length `n`. -/
noncomputable def a091964 (n : ℕ) : ℕ :=
  Nat.card {w : List MotzkinStep // w.length = n ∧ IsPeaklessPrefix w}

/-- Auxiliary Sequence 3 — OEIS A004148: number of peakless Motzkin excursions of length `n`
(RNA secondary structure numbers). -/
noncomputable def a004148 (n : ℕ) : ℕ :=
  Nat.card {w : List MotzkinStep // w.length = n ∧ IsPeaklessPrefix w ∧ prefixHeight w n = 0}

/-- Auxiliary Sequence 4 — OEIS A089735: self-convolution (2-fold Cauchy product) of `A004148`. -/
noncomputable def a089735 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), a004148 k * a004148 (n - k)

/-- Auxiliary Sequence 5 — OEIS A098075: threefold convolution of `A004148` with itself. -/
noncomputable def a098075 (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n - i + 1),
    a004148 i * a004148 j * a004148 (n - i - j)

/-- Auxiliary Sequence 6 — OEIS A097724: Riordan companion triangle counting peakless nonnegative
Motzkin prefixes of length `n` and endpoint height `k`. -/
noncomputable def a097724 (n k : ℕ) : ℕ :=
  Nat.card {w : List MotzkinStep // w.length = n ∧ IsPeaklessPrefix w ∧ prefixHeight w n = (k : ℤ)}

/-! ### 4. Proof Section 1: Monic Rescaled Chebyshev Polynomials `uPoly` and `a192062` -/

/-- Monic rescaled Chebyshev polynomials of the second kind: `u_n(X) = U_n(X / 2) ∈ ℤ[X]`. -/
private noncomputable def uPoly : ℕ → Polynomial ℤ
  | 0 => 1
  | 1 => Polynomial.X
  | n + 2 => Polynomial.X * uPoly (n + 1) - uPoly n

private theorem a192062_even (i j : ℕ) :
    a192062 (2 * i + 2) j = a192062 (2 * i) j + a192062 (2 * i + 1) j := by
  rw [a192062]
  have hmod : (2 * i + 2) % 2 = 0 := by omega
  simp [hmod]

private theorem a192062_odd (i j : ℕ) :
    a192062 (2 * i + 3) j = a192062 (2 * i + 1) j + j * a192062 (2 * i + 2) j := by
  have h : 2 * i + 3 = (2 * i + 1) + 2 := by omega
  rw [h, a192062]
  simp

private theorem a192062_even_recurrence (n j : ℕ) :
    (a192062 (2 * (n + 2) + 2) j : ℤ) =
      ((j : ℤ) + 2) * (a192062 (2 * (n + 1) + 2) j : ℤ) - (a192062 (2 * n + 2) j : ℤ) := by
  have h1 : a192062 (2 * n + 6) j = a192062 (2 * n + 4) j + a192062 (2 * n + 5) j := by
    have := a192062_even (n + 2) j
    rwa [show 2 * (n + 2) + 2 = 2 * n + 6 by omega,
         show 2 * (n + 2) = 2 * n + 4 by omega] at this
  have h2 : a192062 (2 * n + 5) j = a192062 (2 * n + 3) j + j * a192062 (2 * n + 4) j := by
    have := a192062_odd (n + 1) j
    rwa [show 2 * (n + 1) + 3 = 2 * n + 5 by omega,
         show 2 * (n + 1) + 1 = 2 * n + 3 by omega,
         show 2 * (n + 1) + 2 = 2 * n + 4 by omega] at this
  have h3 : a192062 (2 * n + 4) j = a192062 (2 * n + 2) j + a192062 (2 * n + 3) j := by
    have := a192062_even (n + 1) j
    rwa [show 2 * (n + 1) + 2 = 2 * n + 4 by omega,
         show 2 * (n + 1) = 2 * n + 2 by omega] at this
  rw [show 2 * (n + 2) + 2 = 2 * n + 6 by omega,
      show 2 * (n + 1) + 2 = 2 * n + 4 by omega]
  have h1z : (a192062 (2 * n + 6) j : ℤ) =
      (a192062 (2 * n + 4) j : ℤ) + (a192062 (2 * n + 5) j : ℤ) := by exact_mod_cast h1
  have h2z : (a192062 (2 * n + 5) j : ℤ) =
      (a192062 (2 * n + 3) j : ℤ) + (j : ℤ) * (a192062 (2 * n + 4) j : ℤ) := by exact_mod_cast h2
  have h3z : (a192062 (2 * n + 4) j : ℤ) =
      (a192062 (2 * n + 2) j : ℤ) + (a192062 (2 * n + 3) j : ℤ) := by exact_mod_cast h3
  linarith

private theorem a192062_even_eq_uPoly (n j : ℕ) :
    (a192062 (2 * n + 2) j : ℤ) = (uPoly n).eval ((j : ℤ) + 2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 =>
      have h0 : a192062 2 j = 1 := by
        rw [show (2 : ℕ) = 2 * 0 + 2 from rfl, a192062_even 0 j]
        rfl
      simp [uPoly, h0]
    | 1 =>
      have h2 : a192062 2 j = 1 := by
        rw [show (2 : ℕ) = 2 * 0 + 2 from rfl, a192062_even 0 j]
        rfl
      have h3 : a192062 3 j = 1 + j := by
        rw [show (3 : ℕ) = 2 * 0 + 3 from rfl, a192062_odd 0 j, h2]
        simp [a192062]
      have h4 : a192062 4 j = j + 2 := by
        rw [show (4 : ℕ) = 2 * 1 + 2 from rfl, a192062_even 1 j, h2, h3]
        omega
      simp [uPoly, h4]
    | m + 2 =>
      rw [a192062_even_recurrence m j]
      rw [ih (m + 1) (by omega), ih m (by omega)]
      simp [uPoly]

private theorem uPoly_monic_and_natDegree (n : ℕ) :
    (uPoly n).Monic ∧ (uPoly n).natDegree = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => exact ⟨Polynomial.monic_one, Polynomial.natDegree_one⟩
    | 1 => exact ⟨Polynomial.monic_X, Polynomial.natDegree_X⟩
    | m + 2 =>
      obtain ⟨hm1, hd1⟩ := ih (m + 1) (by omega)
      obtain ⟨hm0, hd0⟩ := ih m (by omega)
      have hX_monic : (Polynomial.X * uPoly (m + 1)).Monic := Polynomial.monic_X.mul hm1
      have hX_deg : (Polynomial.X * uPoly (m + 1)).natDegree = m + 2 := by
        rw [Polynomial.natDegree_X_mul hm1.ne_zero, hd1]
      have hdeg_lt : (uPoly m).degree < (Polynomial.X * uPoly (m + 1)).degree := by
        rw [Polynomial.degree_eq_natDegree hm0.ne_zero,
            Polynomial.degree_eq_natDegree hX_monic.ne_zero, hd0, hX_deg]
        exact_mod_cast (show m < m + 2 by omega)
      refine ⟨hX_monic.sub_of_left hdeg_lt, ?_⟩
      rw [uPoly, Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by omega), hX_deg]

private theorem uPoly_linearIndependent :
    ∀ (m : ℕ) (c : ℕ → ℤ),
      (∑ k ∈ Finset.range m, Polynomial.C (c k) * uPoly k) = 0 →
      ∀ k < m, c k = 0 := by
  intro m
  induction m with
  | zero =>
    intro _ _ k hk
    omega
  | succ m ih =>
    intro c hsum
    have hcm : c m = 0 := by
      have hcoeff := congrArg (fun p : Polynomial ℤ => p.coeff m) hsum
      simp only [Polynomial.coeff_zero, Finset.sum_range_succ, Polynomial.finsetSum_coeff,
        Polynomial.coeff_add, Polynomial.coeff_C_mul] at hcoeff
      have hprev : ∑ k ∈ Finset.range m, c k * (uPoly k).coeff m = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        have hkm : k < m := Finset.mem_range.mp hk
        have hd : (uPoly k).natDegree < m := by
          rw [(uPoly_monic_and_natDegree k).2]
          exact hkm
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hd, mul_zero]
      have htop : (uPoly m).coeff m = 1 := by
        obtain ⟨hm, hd⟩ := uPoly_monic_and_natDegree m
        rw [← hm.leadingCoeff, ← Polynomial.coeff_natDegree, hd]
      rw [hprev, zero_add, htop, mul_one] at hcoeff
      exact hcoeff
    have hsum' : (∑ k ∈ Finset.range m, Polynomial.C (c k) * uPoly k) = 0 := by
      rw [Finset.sum_range_succ, hcm, map_zero, zero_mul, add_zero] at hsum
      exact hsum
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
    · exact ih c hsum' k hlt
    · exact hcm

private theorem isA191579Row_unique {n : ℕ} {r₁ r₂ : ℕ → ℕ}
    (h1 : IsA191579Row n r₁) (h2 : IsA191579Row n r₂) : r₁ = r₂ := by
  let P : Polynomial ℤ :=
    ∑ k ∈ Finset.range (n + 1), Polynomial.C ((r₁ k : ℤ) - (r₂ k : ℤ)) * uPoly k
  have hroot : ∀ j : ℕ, P.IsRoot ((j : ℤ) + 2) := by
    intro j
    rw [Polynomial.IsRoot.def]
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
    have heq : ∑ k ∈ Finset.range (n + 1), r₁ k * a192062 (2 * k + 2) j =
        ∑ k ∈ Finset.range (n + 1), r₂ k * a192062 (2 * k + 2) j :=
      (h1.2 j).symm.trans (h2.2 j)
    have heqz : (∑ k ∈ Finset.range (n + 1), (r₁ k : ℤ) * (a192062 (2 * k + 2) j : ℤ)) =
        ∑ k ∈ Finset.range (n + 1), (r₂ k : ℤ) * (a192062 (2 * k + 2) j : ℤ) := by
      exact_mod_cast heq
    have hsub :
        ∑ k ∈ Finset.range (n + 1), ((r₁ k : ℤ) - (r₂ k : ℤ)) * (uPoly k).eval ((j : ℤ) + 2) =
        (∑ k ∈ Finset.range (n + 1), (r₁ k : ℤ) * (a192062 (2 * k + 2) j : ℤ)) -
        (∑ k ∈ Finset.range (n + 1), (r₂ k : ℤ) * (a192062 (2 * k + 2) j : ℤ)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← a192062_even_eq_uPoly k j]
      ring
    rw [hsub, heqz, sub_self]
  have hinf : Set.Infinite {x : ℤ | P.IsRoot x} := by
    have hinj : Function.Injective (fun j : ℕ => (j : ℤ) + 2) := fun a b hab => by
      dsimp only at hab
      omega
    exact (Set.infinite_range_of_injective hinj).mono (by
      rintro _ ⟨j, rfl⟩
      exact hroot j)
  have hP0 : P = 0 := Polynomial.eq_zero_of_infinite_isRoot P hinf
  have hdiff := uPoly_linearIndependent (n + 1) (fun k => (r₁ k : ℤ) - (r₂ k : ℤ)) hP0
  funext k
  by_cases hk : k ≤ n
  · have := hdiff k (by omega)
    omega
  · rw [h1.1 k (by omega), h2.1 k (by omega)]

/-! ### 5. Proof Section 2: Combinatorial Toolkit for Peakless Motzkin Paths -/

private instance : Fintype MotzkinStep where
  elems := {.U, .H, .D}
  complete x := by cases x <;> simp

private theorem finite_motzkin_len (n : ℕ) (P : List MotzkinStep → Prop) :
    Finite {w : List MotzkinStep // w.length = n ∧ P w} := by
  let f : {w : List MotzkinStep // w.length = n ∧ P w} → (Fin n → MotzkinStep) :=
    fun w i => w.1[i.val]'(by omega)
  refine Finite.of_injective f ?_
  intro a b hab
  apply Subtype.ext
  apply List.ext_getElem (by rw [a.2.1, b.2.1])
  intro i hia hib
  have := congrFun hab ⟨i, by omega⟩
  simpa [f] using this

private theorem subtype_heq {α : Type*} {p q : α → Prop} {a b : α}
    {ha : p a} {hb : q b} (hpq : p = q) (hab : a = b) :
    HEq (⟨a, ha⟩ : Subtype p) (⟨b, hb⟩ : Subtype q) := by
  subst hpq; subst hab; rfl

private theorem sigma_prod_ext {α : Type*} {P Q : α → Type*}
    {a b : α} {p₁ : P a} {q₁ : Q a} {p₂ : P b} {q₂ : Q b}
    (hab : a = b) (hp : HEq p₁ p₂) (hq : HEq q₁ q₂) :
    (⟨a, (p₁, q₁)⟩ : Σ x, P x × Q x) = ⟨b, (p₂, q₂)⟩ := by
  subst hab; cases hp; cases hq; rfl

private theorem prefixHeight_zero (w : List MotzkinStep) : prefixHeight w 0 = 0 := by
  simp [prefixHeight]

private theorem prefixHeight_append_left (u v : List MotzkinStep) {i : ℕ} (hi : i ≤ u.length) :
    prefixHeight (u ++ v) i = prefixHeight u i := by
  simp [prefixHeight, List.take_append_of_le_length hi]

private theorem prefixHeight_append_right (u v : List MotzkinStep) (j : ℕ) :
    prefixHeight (u ++ v) (u.length + j) = prefixHeight u u.length + prefixHeight v j := by
  unfold prefixHeight
  rw [List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, List.take_of_length_le (le_refl _),
      List.map_append, List.sum_append]

private theorem prefixHeight_succ (w : List MotzkinStep) {i : ℕ} (hi : i < w.length) :
    prefixHeight w (i + 1) = prefixHeight w i + w[i].delta := by
  unfold prefixHeight
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append]
  simp

private theorem prefixHeight_le_length (w : List MotzkinStep) :
    prefixHeight w w.length ≤ (w.length : ℤ) := by
  unfold prefixHeight
  rw [List.take_of_length_le (le_refl w.length)]
  induction w with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hx : x.delta ≤ 1 := by cases x <;> decide
    omega

private theorem isPeakless_iff_forall (w : List MotzkinStep) :
    IsPeakless w ↔ ∀ i (hi : i + 1 < w.length), w[i] = .U → w[i + 1] ≠ .D := by
  induction w with
  | nil => simp [IsPeakless]
  | cons x xs ih =>
    cases xs with
    | nil => simp [IsPeakless]
    | cons y ys =>
      rw [IsPeakless, ih]
      constructor
      · rintro ⟨hxy, htail⟩ i hi
        cases i with
        | zero => exact hxy
        | succ j => exact htail j (by simpa using hi)
      · intro hall
        refine ⟨hall 0 (by simp), fun j hj => ?_⟩
        exact hall (j + 1) (by simpa using hj)

private theorem isPeakless_take {w : List MotzkinStep} (hw : IsPeakless w) (m : ℕ) :
    IsPeakless (w.take m) := by
  rw [isPeakless_iff_forall] at hw ⊢
  intro i hi hU
  have hiw : i + 1 < w.length := by
    rw [List.length_take] at hi
    omega
  have h1 : (w.take m)[i] = w[i] := List.getElem_take
  have h2 : (w.take m)[i + 1] = w[i + 1] := List.getElem_take
  rw [h1] at hU
  rw [h2]
  exact hw i hiw hU

private theorem isPeakless_drop {w : List MotzkinStep} (hw : IsPeakless w) (m : ℕ) :
    IsPeakless (w.drop m) := by
  rw [isPeakless_iff_forall] at hw ⊢
  intro i hi hU
  have hiw : m + i + 1 < w.length := by
    rw [List.length_drop] at hi
    omega
  have h1 : (w.drop m)[i] = w[m + i] := List.getElem_drop
  have h2 : (w.drop m)[i + 1] = w[m + i + 1] := by
    simp [Nat.add_assoc]
  rw [h1] at hU
  rw [h2]
  exact hw (m + i) hiw hU

private theorem isPeakless_append_iff (u v : List MotzkinStep) :
    IsPeakless (u ++ v) ↔
      IsPeakless u ∧ IsPeakless v ∧
        (∀ (hu : 0 < u.length) (hv : 0 < v.length), u[u.length - 1] = .U → v[0] ≠ .D) := by
  rw [isPeakless_iff_forall, isPeakless_iff_forall, isPeakless_iff_forall]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i hi hU
      have hi' : i + 1 < (u ++ v).length := by simp; omega
      have h1 : (u ++ v)[i] = u[i] := List.getElem_append_left (by omega)
      have h2 : (u ++ v)[i + 1] = u[i + 1] := List.getElem_append_left hi
      exact h2 ▸ h i hi' (h1.trans hU)
    · intro i hi hU
      have hi' : u.length + i + 1 < (u ++ v).length := by simp; omega
      have h1 : (u ++ v)[u.length + i] = v[i] := by
        rw [List.getElem_append_right (by omega)]
        simp
      have h2 : (u ++ v)[u.length + i + 1] = v[i + 1] := by
        rw [List.getElem_append_right (by omega)]
        simp [Nat.add_assoc]
      exact h2 ▸ h (u.length + i) hi' (h1.trans hU)
    · intro hu hv hU
      have hi' : u.length - 1 + 1 < (u ++ v).length := by simp; omega
      have h1 : (u ++ v)[u.length - 1] = u[u.length - 1] := List.getElem_append_left (by omega)
      have h2 : (u ++ v)[u.length - 1 + 1] = v[0] := by
        rw [List.getElem_append_right (by omega)]
        simp [show u.length - 1 + 1 - u.length = 0 by omega]
      exact h2 ▸ h (u.length - 1) hi' (h1.trans hU)
  · rintro ⟨hu, hv, hbd⟩ i hi hU
    by_cases hlt : i + 1 < u.length
    · have h1 : (u ++ v)[i] = u[i] := List.getElem_append_left (by omega)
      have h2 : (u ++ v)[i + 1] = u[i + 1] := List.getElem_append_left hlt
      rw [h1] at hU
      rw [h2]
      exact hu i hlt hU
    · by_cases heq : i + 1 = u.length
      · have hu_pos : 0 < u.length := by omega
        have hv_pos : 0 < v.length := by simp at hi; omega
        have h1 : (u ++ v)[i] = u[u.length - 1] := by
          rw [List.getElem_append_left (by omega)]
          congr 1
          omega
        have h2 : (u ++ v)[i + 1] = v[0] := by
          rw [List.getElem_append_right (by omega)]
          simp [heq]
        rw [h1] at hU
        rw [h2]
        exact hbd hu_pos hv_pos hU
      · have hge : u.length ≤ i := by omega
        have hvi : i - u.length + 1 < v.length := by simp at hi; omega
        have h1 : (u ++ v)[i] = v[i - u.length] := List.getElem_append_right hge
        have h2 : (u ++ v)[i + 1] = v[i - u.length + 1] := by
          rw [List.getElem_append_right (by omega)]
          congr 1
          omega
        rw [h1] at hU
        rw [h2]
        exact hv (i - u.length) hvi hU

private theorem first_ne_D_of_prefix {w : List MotzkinStep}
    (hw : IsPeaklessPrefix w) (hpos : 0 < w.length) : w[0] ≠ .D := by
  have h1 : 0 ≤ prefixHeight w 1 := hw.1 1 hpos
  rw [prefixHeight_succ w hpos, prefixHeight_zero, zero_add] at h1
  intro hD
  rw [hD] at h1
  exact absurd h1 (by decide)

private theorem last_ne_U_of_excursion {w : List MotzkinStep}
    (hw : IsPeaklessPrefix w) (h0 : prefixHeight w w.length = 0) (hpos : 0 < w.length) :
    w[w.length - 1] ≠ .U := by
  have hprev : 0 ≤ prefixHeight w (w.length - 1) := hw.1 (w.length - 1) (by omega)
  have hstep := prefixHeight_succ w (i := w.length - 1) (by omega)
  have heq : w.length - 1 + 1 = w.length := by omega
  rw [heq, h0] at hstep
  intro hU
  rw [hU, MotzkinStep.delta] at hstep
  omega

private theorem list_eq_take_append_last {α : Type*} (w : List α) (n : ℕ)
    (hlen : w.length = n + 1) :
    w = w.take n ++ [w[n]'(by omega)] := by
  have := List.take_succ_eq_append_getElem (l := w) (i := n) (h := by omega)
  rw [← hlen, List.take_of_length_le (le_refl w.length)] at this
  exact this

private theorem list_split_at_mid {α : Type*} (w : List α) {m : ℕ} (hm : m < w.length) :
    w = w.take m ++ [w[m]] ++ w.drop (m + 1) := by
  calc w = w.take m ++ w.drop m := (List.take_append_drop m w).symm
    _ = w.take m ++ (w[m] :: w.drop (m + 1)) := by rw [List.drop_eq_getElem_cons hm]
    _ = w.take m ++ [w[m]] ++ w.drop (m + 1) := by simp

/-- Largest index `i ≤ N + 1` where `prefixHeight w i = 0`. -/
private noncomputable def lastZeroIdx (w : List MotzkinStep) (N : ℕ) : ℕ :=
  ((Finset.range (N + 2)).filter (fun i => prefixHeight w i = 0)).max'
    ⟨0, by simp [prefixHeight_zero]⟩

private theorem lastZeroIdx_le_succ (w : List MotzkinStep) (N : ℕ) :
    lastZeroIdx w N ≤ N + 1 := by
  have hmem := Finset.max'_mem ((Finset.range (N + 2)).filter (fun i => prefixHeight w i = 0))
    ⟨0, by simp [prefixHeight_zero]⟩
  have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hmem).1
  change lastZeroIdx w N < N + 2 at hlt
  omega

private theorem prefixHeight_lastZeroIdx (w : List MotzkinStep) (N : ℕ) :
    prefixHeight w (lastZeroIdx w N) = 0 := by
  have hmem := Finset.max'_mem ((Finset.range (N + 2)).filter (fun i => prefixHeight w i = 0))
    ⟨0, by simp [prefixHeight_zero]⟩
  exact (Finset.mem_filter.mp hmem).2

private theorem lastZeroIdx_le {w : List MotzkinStep} {N : ℕ}
    (hpos : 0 < prefixHeight w (N + 1)) : lastZeroIdx w N ≤ N := by
  have hle := lastZeroIdx_le_succ w N
  have hz := prefixHeight_lastZeroIdx w N
  by_contra hgt
  have heq : lastZeroIdx w N = N + 1 := by omega
  rw [heq] at hz
  omega

private theorem one_le_prefixHeight_of_gt_lastZeroIdx {w : List MotzkinStep} {N : ℕ}
    (hnonneg : ∀ i ≤ N + 1, 0 ≤ prefixHeight w i) {i : ℕ}
    (h1 : lastZeroIdx w N < i) (h2 : i ≤ N + 1) : 1 ≤ prefixHeight w i := by
  have hi_nonneg := hnonneg i h2
  have hi_ne : prefixHeight w i ≠ 0 := by
    intro hz
    have hiS : i ∈ (Finset.range (N + 2)).filter (fun j => prefixHeight w j = 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hz⟩
    have := Finset.le_max' ((Finset.range (N + 2)).filter (fun j => prefixHeight w j = 0)) i hiS
    change i ≤ lastZeroIdx w N at this
    omega
  omega

private theorem getElem_lastZeroIdx_eq_U {w : List MotzkinStep} {N : ℕ}
    (hlen : N + 1 ≤ w.length)
    (hnonneg : ∀ i ≤ N + 1, 0 ≤ prefixHeight w i)
    (hpos : 0 < prefixHeight w (N + 1)) :
    w[lastZeroIdx w N]'(by have := lastZeroIdx_le hpos; omega) = MotzkinStep.U := by
  have hle := lastZeroIdx_le hpos
  have h1 := one_le_prefixHeight_of_gt_lastZeroIdx hnonneg (i := lastZeroIdx w N + 1)
    (by omega) (by omega)
  rw [prefixHeight_succ w (by omega), prefixHeight_lastZeroIdx, zero_add] at h1
  cases hwm : w[lastZeroIdx w N]'(by omega) with
  | U => rfl
  | H => rw [hwm] at h1; exact absurd h1 (by decide)
  | D => rw [hwm] at h1; exact absurd h1 (by decide)

private theorem lastZeroIdx_eq {w : List MotzkinStep} {N m : ℕ}
    (hm : m ≤ N + 1) (hz : prefixHeight w m = 0)
    (hgt : ∀ i, m < i → i ≤ N + 1 → prefixHeight w i ≠ 0) :
    lastZeroIdx w N = m := by
  let S := (Finset.range (N + 2)).filter (fun i => prefixHeight w i = 0)
  have h0S : 0 ∈ S := by simp [S, prefixHeight_zero]
  have hmS : m ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hz⟩
  apply le_antisymm
  · refine Finset.max'_le S ⟨0, h0S⟩ m fun i hi => ?_
    have hi_lt := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hi_z := (Finset.mem_filter.mp hi).2
    by_contra hlt
    exact hgt i (by omega) (by omega) hi_z
  · exact Finset.le_max' S m hmS

private abbrev Exc (n : ℕ) :=
  {w : List MotzkinStep // w.length = n ∧ IsPeaklessPrefix w ∧ prefixHeight w n = 0}

private abbrev PrefH (n k : ℕ) :=
  {w : List MotzkinStep // w.length = n ∧ IsPeaklessPrefix w ∧ prefixHeight w n = (k : ℤ)}

private abbrev Pref (n : ℕ) :=
  {w : List MotzkinStep // w.length = n ∧ IsPeaklessPrefix w}

private theorem exc_heq {n m : ℕ} {a : Exc n} {b : Exc m}
    (hnm : n = m) (hab : a.1 = b.1) : HEq a b := by
  subst hnm; exact heq_of_eq (Subtype.ext hab)

private theorem prefH_heq {n m k : ℕ} {a : PrefH n k} {b : PrefH m k}
    (hnm : n = m) (hab : a.1 = b.1) : HEq a b := by
  subst hnm; exact heq_of_eq (Subtype.ext hab)

private theorem a004148_zero : a004148 0 = 1 := by
  unfold a004148
  have : Unique (Exc 0) :=
    { default := ⟨[], rfl, ⟨fun i hi => by
          have : i = 0 := by simpa using hi
          subst this; simp [prefixHeight], trivial⟩, rfl⟩
      uniq := fun ⟨w, hlen, _, _⟩ => by
        apply Subtype.ext
        exact List.eq_nil_of_length_eq_zero hlen }
  exact Nat.card_unique

private theorem a004148_one : a004148 1 = 1 := by
  unfold a004148
  have hH : IsPeaklessPrefix [MotzkinStep.H] := by
    refine ⟨fun i hi => ?_, trivial⟩
    have : i = 0 ∨ i = 1 := by simp at hi; omega
    rcases this with rfl | rfl <;> decide
  have : Unique (Exc 1) :=
    { default := ⟨[MotzkinStep.H], rfl, hH, rfl⟩
      uniq := fun ⟨w, hlen, _, h0⟩ => by
        apply Subtype.ext
        cases w with
        | nil => simp at hlen
        | cons x xs =>
          have hxs : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
          subst hxs
          cases x with
          | H => rfl
          | U => simp [prefixHeight, MotzkinStep.delta] at h0
          | D => simp [prefixHeight, MotzkinStep.delta] at h0 }
  exact Nat.card_unique

/-- Step 5 (Excursion decomposition): for every `n : ℕ`,
`Exc (n + 2) ≃ Exc (n + 1) ⊕ Σ k : Fin n, Exc (k.val + 1) × Exc (n - 1 - k.val)`. -/
private noncomputable def excDecompEquiv (n : ℕ) :
    Exc (n + 2) ≃ Exc (n + 1) ⊕ Σ k : Fin n, Exc (k.val + 1) × Exc (n - 1 - k.val) := by
  refine
    { toFun := fun ⟨w, hlen, hpref, h0⟩ =>
        if hlast : w[n + 1]'(by omega) = MotzkinStep.H then
          Sum.inl ⟨w.take (n + 1), by simp [hlen],
            ⟨fun i hi => by
                rw [List.length_take_of_le (by omega)] at hi
                have hw := list_eq_take_append_last w (n + 1) hlen
                have hph : prefixHeight (w.take (n + 1)) i = prefixHeight w i := by
                  conv_rhs => rw [hw]
                  rw [prefixHeight_append_left _ _ (by simp [hlen]; omega)]
                rw [hph]
                exact hpref.1 i (by omega),
              isPeakless_take hpref.2 (n + 1)⟩,
            by
              have hw := list_eq_take_append_last w (n + 1) hlen
              have hstep := prefixHeight_succ w (i := n + 1) (by omega)
              rw [h0, hlast, MotzkinStep.delta, add_zero] at hstep
              have hph : prefixHeight (w.take (n + 1)) (n + 1) = prefixHeight w (n + 1) := by
                conv_rhs => rw [hw]
                rw [prefixHeight_append_left _ _ (by simp [hlen])]
              omega⟩
        else
          have hlastD : w[n + 1]'(by omega) = MotzkinStep.D := by
            have hstep := prefixHeight_succ w (i := n + 1) (by omega)
            have hprev := hpref.1 (n + 1) (by omega)
            rw [h0] at hstep
            cases hwn : w[n + 1]'(by omega) with
            | D => rfl
            | H => exact absurd hwn hlast
            | U => rw [hwn, MotzkinStep.delta] at hstep; omega
          have hph_n1 : prefixHeight w (n + 1) = 1 := by
            have hstep := prefixHeight_succ w (i := n + 1) (by omega)
            rw [h0, hlastD, MotzkinStep.delta] at hstep
            omega
          let m := lastZeroIdx w n
          have hm_le_n : m ≤ n := lastZeroIdx_le (by omega)
          have hm_zero : prefixHeight w m = 0 := prefixHeight_lastZeroIdx w n
          have hnonneg_n1 : ∀ i ≤ n + 1, 0 ≤ prefixHeight w i := fun i hi => hpref.1 i (by omega)
          have hmU : w[m]'(by omega) = MotzkinStep.U :=
            getElem_lastZeroIdx_eq_U (by omega) hnonneg_n1 (by omega)
          have hm_lt_n : m < n := by
            by_contra hge
            have hmn : m = n := by omega
            have hpk := (isPeakless_iff_forall w).mp hpref.2 m (by omega) hmU
            have : w[m + 1]'(by omega) = MotzkinStep.D := by simpa [hmn] using hlastD
            exact hpk this
          let k : Fin n := ⟨n - 1 - m, by omega⟩
          let w₁ : List MotzkinStep := w.take m
          let w₂ : List MotzkinStep := (w.drop (m + 1)).take (k.val + 1)
          have hw_decomp : w = w₁ ++ [MotzkinStep.U] ++ w₂ ++ [MotzkinStep.D] := by
            have hmid := list_split_at_mid w (m := m) (by omega)
            rw [hmU] at hmid
            have hdrop_len : (w.drop (m + 1)).length = (k.val + 1) + 1 := by
              simp [hlen, k]; omega
            have hdrop_eq := list_eq_take_append_last (w.drop (m + 1)) (k.val + 1) hdrop_len
            have hdrop_last : (w.drop (m + 1))[k.val + 1]'(by omega) = MotzkinStep.D := by
              rw [List.getElem_drop]
              have hidx : m + 1 + (k.val + 1) = n + 1 := by simp [k]; omega
              simpa [hidx] using hlastD
            rw [hdrop_last] at hdrop_eq
            calc w = w₁ ++ [MotzkinStep.U] ++ w.drop (m + 1) := hmid
              _ = w₁ ++ [MotzkinStep.U] ++ (w₂ ++ [MotzkinStep.D]) := by rw [hdrop_eq]
              _ = w₁ ++ [MotzkinStep.U] ++ w₂ ++ [MotzkinStep.D] := by simp [List.append_assoc]
          have hw1_len : w₁.length = n - 1 - k.val := by simp [w₁, hlen, k]; omega
          have hw2_len : w₂.length = k.val + 1 := by simp [w₂, hlen, k]; omega
          have hph1 : ∀ i ≤ m, prefixHeight w₁ i = prefixHeight w i := fun i hi => by
            conv_rhs => rw [hw_decomp, List.append_assoc, List.append_assoc]
            rw [prefixHeight_append_left w₁ _ (by simp [w₁, hlen]; omega)]
          have hw1_z : prefixHeight w₁ (n - 1 - k.val) = 0 := by
            have hm_eq : n - 1 - k.val = m := by simp [k]; omega
            rw [hm_eq, hph1 m (le_refl m), hm_zero]
          have hph2 : ∀ r ≤ k.val + 1,
              prefixHeight w (m + 1 + r) = 1 + prefixHeight w₂ r := fun r hr => by
            have hleft : (w₁ ++ [MotzkinStep.U]).length = m + 1 := by simp [w₁, hlen]; omega
            have hleft_ph : prefixHeight (w₁ ++ [MotzkinStep.U]) (m + 1) = 1 := by
              rw [show m + 1 = w₁.length + 1 by simp [w₁, hlen]; omega,
                  prefixHeight_append_right, hw1_len, hw1_z]
              rfl
            have hw_eq : w = (w₁ ++ [MotzkinStep.U]) ++ (w₂ ++ [MotzkinStep.D]) := by
              rw [hw_decomp]; simp [List.append_assoc]
            rw [hw_eq, ← hleft, prefixHeight_append_right, hleft, hleft_ph,
                prefixHeight_append_left w₂ [MotzkinStep.D] (by omega)]
          Sum.inr ⟨k,
            ⟨w₂, hw2_len,
              ⟨fun r hr => by
                  rw [hw2_len] at hr
                  have h1 := one_le_prefixHeight_of_gt_lastZeroIdx hnonneg_n1
                    (i := m + 1 + r) (by omega) (by simp [k] at hr; omega)
                  rw [hph2 r hr] at h1
                  omega,
                isPeakless_take (isPeakless_drop hpref.2 (m + 1)) (k.val + 1)⟩,
              by
                have h1 := hph2 (k.val + 1) (le_refl _)
                have hidx : m + 1 + (k.val + 1) = n + 1 := by simp [k]; omega
                rw [hidx, hph_n1] at h1
                omega⟩,
            ⟨w₁, hw1_len,
              ⟨fun i hi => by
                  rw [hw1_len] at hi
                  rw [hph1 i (by simp [k] at hi; omega)]
                  exact hpref.1 i (by simp [k] at hi; omega),
                isPeakless_take hpref.2 m⟩,
              hw1_z⟩⟩
      invFun := fun
        | Sum.inl ⟨w, hlen, hpref, h0⟩ =>
          ⟨w ++ [MotzkinStep.H], by simp [hlen],
            ⟨fun i hi => by
                simp [hlen] at hi
                by_cases hle : i ≤ n + 1
                · rw [prefixHeight_append_left w [MotzkinStep.H] (by omega)]
                  exact hpref.1 i (by omega)
                · have heq : i = w.length + 1 := by omega
                  rw [heq, prefixHeight_append_right, hlen, h0]
                  decide,
              (isPeakless_append_iff w [MotzkinStep.H]).mpr ⟨hpref.2, trivial, fun _ _ _ => by simp⟩⟩,
            by
              rw [show n + 2 = w.length + 1 by omega, prefixHeight_append_right, hlen, h0]
              rfl⟩
        | Sum.inr ⟨k, ⟨w₂, hlen2, hpref2, h02⟩, ⟨w₁, hlen1, hpref1, h01⟩⟩ =>
          let w : List MotzkinStep := w₁ ++ [MotzkinStep.U] ++ w₂ ++ [MotzkinStep.D]
          have hlen : w.length = n + 2 := by simp [w, hlen1, hlen2]; omega
          have hph_mid : ∀ r ≤ k.val + 1,
              prefixHeight w (w₁.length + 1 + r) = 1 + prefixHeight w₂ r := fun r hr => by
            have hl : (w₁ ++ [MotzkinStep.U]).length = w₁.length + 1 := by simp
            have hlp : prefixHeight (w₁ ++ [MotzkinStep.U]) (w₁.length + 1) = 1 := by
              rw [prefixHeight_append_right, hlen1, h01]
              rfl
            have hw_eq : w = (w₁ ++ [MotzkinStep.U]) ++ (w₂ ++ [MotzkinStep.D]) := by
              simp [w, List.append_assoc]
            rw [hw_eq, ← hl, prefixHeight_append_right, hl, hlp,
                prefixHeight_append_left w₂ [MotzkinStep.D] (by omega)]
          have hpre_1 :
              prefixHeight (w₁ ++ [MotzkinStep.U] ++ w₂) (w₁ ++ [MotzkinStep.U] ++ w₂).length = 1 := by
            have hl : (w₁ ++ [MotzkinStep.U]).length = w₁.length + 1 := by simp
            rw [show (w₁ ++ [MotzkinStep.U] ++ w₂).length = (w₁ ++ [MotzkinStep.U]).length + w₂.length
                  by simp; omega,
                prefixHeight_append_right, hl, prefixHeight_append_right, hlen1, h01, hlen2, h02]
            rfl
          have hph_all : ∀ i ≤ n + 2, 0 ≤ prefixHeight w i := by
            intro i hi
            by_cases hi1 : i ≤ w₁.length
            · have hw_eq : w = w₁ ++ ([MotzkinStep.U] ++ w₂ ++ [MotzkinStep.D]) := by
                simp [w, List.append_assoc]
              rw [hw_eq, prefixHeight_append_left w₁ _ hi1]
              exact hpref1.1 i hi1
            · by_cases hi2 : i ≤ n + 1
              · have hr : i - (w₁.length + 1) ≤ k.val + 1 := by omega
                have heq : i = w₁.length + 1 + (i - (w₁.length + 1)) := by omega
                rw [heq, hph_mid _ hr]
                have := hpref2.1 (i - (w₁.length + 1)) (by omega)
                omega
              · have heq : i = (w₁ ++ [MotzkinStep.U] ++ w₂).length + 1 := by
                  simp [hlen1, hlen2]; omega
                rw [heq, prefixHeight_append_right, hpre_1]
                decide
          have hpeak : IsPeakless w := by
            have h1 : IsPeakless (w₁ ++ [MotzkinStep.U]) :=
              (isPeakless_append_iff w₁ [MotzkinStep.U]).mpr ⟨hpref1.2, trivial, fun _ _ _ => by simp⟩
            have h2 : IsPeakless (w₁ ++ [MotzkinStep.U] ++ w₂) := by
              refine (isPeakless_append_iff (w₁ ++ [MotzkinStep.U]) w₂).mpr
                ⟨h1, hpref2.2, fun _ hv _ => ?_⟩
              exact first_ne_D_of_prefix hpref2 hv
            refine (isPeakless_append_iff (w₁ ++ [MotzkinStep.U] ++ w₂) [MotzkinStep.D]).mpr
              ⟨h2, trivial, fun _ _ hU => ?_⟩
            have hw2_pos : 0 < w₂.length := by omega
            have hlast_eq :
                (w₁ ++ [MotzkinStep.U] ++ w₂)[(w₁ ++ [MotzkinStep.U] ++ w₂).length - 1]'(by simp) =
                w₂[w₂.length - 1]'(by omega) := by
              rw [List.getElem_append_right (by simp; omega)]
              congr 1
              simp
              omega
            rw [hlast_eq] at hU
            exact absurd hU (last_ne_U_of_excursion hpref2 (by simpa [hlen2] using h02) hw2_pos)
          have h0 : prefixHeight w (n + 2) = 0 := by
            have heq : n + 2 = (w₁ ++ [MotzkinStep.U] ++ w₂).length + 1 := by
              simp [hlen1, hlen2]; omega
            rw [heq, prefixHeight_append_right, hpre_1]
            rfl
          ⟨w, hlen, ⟨fun i hi => hph_all i (by omega), hpeak⟩, h0⟩
      left_inv := by
        rintro ⟨w, hlen, hpref, h0⟩
        dsimp only
        split_ifs with hlast
        · apply Subtype.ext
          dsimp only
          have hw := list_eq_take_append_last w (n + 1) hlen
          rw [hlast] at hw
          exact hw.symm
        · apply Subtype.ext
          dsimp only
          have hlastD : w[n + 1]'(by omega) = MotzkinStep.D := by
            have hstep := prefixHeight_succ w (i := n + 1) (by omega)
            have hprev := hpref.1 (n + 1) (by omega)
            rw [h0] at hstep
            cases hwn : w[n + 1]'(by omega) with
            | D => rfl
            | H => exact absurd hwn hlast
            | U => rw [hwn, MotzkinStep.delta] at hstep; omega
          have hph_n1 : prefixHeight w (n + 1) = 1 := by
            have hstep := prefixHeight_succ w (i := n + 1) (by omega)
            rw [h0, hlastD, MotzkinStep.delta] at hstep
            omega
          let m := lastZeroIdx w n
          have hm_le_n : m ≤ n := lastZeroIdx_le (by omega)
          have hnonneg_n1 : ∀ i ≤ n + 1, 0 ≤ prefixHeight w i := fun i hi => hpref.1 i (by omega)
          have hmU : w[m]'(by omega) = MotzkinStep.U :=
            getElem_lastZeroIdx_eq_U (by omega) hnonneg_n1 (by omega)
          have hm_lt_n : m < n := by
            by_contra hge
            have hmn : m = n := by omega
            have hpk := (isPeakless_iff_forall w).mp hpref.2 m (by omega) hmU
            have : w[m + 1]'(by omega) = MotzkinStep.D := by simpa [hmn] using hlastD
            exact hpk this
          have hmid := list_split_at_mid w (m := m) (by omega)
          rw [hmU] at hmid
          have hdrop_len : (w.drop (m + 1)).length = (n - 1 - m + 1) + 1 := by
            simp [hlen]; omega
          have hdrop_eq := list_eq_take_append_last (w.drop (m + 1)) (n - 1 - m + 1) hdrop_len
          have hdrop_last : (w.drop (m + 1))[n - 1 - m + 1]'(by omega) = MotzkinStep.D := by
            rw [List.getElem_drop]
            have hidx : m + 1 + (n - 1 - m + 1) = n + 1 := by omega
            simpa [hidx] using hlastD
          rw [hdrop_last] at hdrop_eq
          symm
          calc w = w.take m ++ [MotzkinStep.U] ++ w.drop (m + 1) := hmid
            _ = w.take m ++ [MotzkinStep.U] ++
                  ((w.drop (m + 1)).take (n - 1 - m + 1) ++ [MotzkinStep.D]) := by
                conv_lhs => rw [hdrop_eq]
            _ = w.take m ++ [MotzkinStep.U] ++
                  (w.drop (m + 1)).take (n - 1 - m + 1) ++ [MotzkinStep.D] := by
                simp [List.append_assoc]
      right_inv := by
        rintro (⟨w, hlen, hpref, h0⟩ | ⟨k, ⟨w₂, hlen2, hpref2, h02⟩, ⟨w₁, hlen1, hpref1, h01⟩⟩)
        · dsimp only
          have hlast : (w ++ [MotzkinStep.H])[n + 1]'(by simp [hlen]) = MotzkinStep.H := by
            rw [List.getElem_append_right (by omega)]
            simp [hlen]
          rw [dite_eq_left_of_eq_true (eq_true hlast)]
          congr 1
          apply Subtype.ext
          simp [List.take_append_of_le_length (le_of_eq hlen.symm), hlen]
        · dsimp only
          let w : List MotzkinStep := w₁ ++ [MotzkinStep.U] ++ w₂ ++ [MotzkinStep.D]
          have hlastD : w[n + 1]'(by simp [w, hlen1, hlen2]; omega) = MotzkinStep.D := by
            rw [List.getElem_append_right (by simp [hlen1, hlen2]; omega)]
            simp
          have hlast_ne : ¬ w[n + 1]'(by simp [w, hlen1, hlen2]; omega) = MotzkinStep.H := by
            rw [hlastD]; decide
          rw [dite_eq_right_of_eq_false (eq_false hlast_ne)]
          congr 1
          have hm_eq : lastZeroIdx w n = n - 1 - k.val := by
            refine lastZeroIdx_eq (by omega) ?_ ?_
            · have hw_eq : w = w₁ ++ ([MotzkinStep.U] ++ w₂ ++ [MotzkinStep.D]) := by
                simp [w, List.append_assoc]
              rw [hw_eq, prefixHeight_append_left w₁ _ (by omega), h01]
            · intro i hgt hiN
              have hr : i - (w₁.length + 1) ≤ k.val + 1 := by omega
              have heq : i = w₁.length + 1 + (i - (w₁.length + 1)) := by omega
              have hl : (w₁ ++ [MotzkinStep.U]).length = w₁.length + 1 := by simp
              have hlp : prefixHeight (w₁ ++ [MotzkinStep.U]) (w₁.length + 1) = 1 := by
                rw [prefixHeight_append_right, hlen1, h01]; rfl
              have hw_eq : w = (w₁ ++ [MotzkinStep.U]) ++ (w₂ ++ [MotzkinStep.D]) := by
                simp [w, List.append_assoc]
              have hpos : prefixHeight w i = 1 + prefixHeight w₂ (i - (w₁.length + 1)) := by
                conv_lhs => rw [heq, hw_eq, ← hl]
                rw [prefixHeight_append_right, hl, hlp,
                    prefixHeight_append_left w₂ [MotzkinStep.D] (by omega)]
              have := hpref2.1 (i - (w₁.length + 1)) (by omega)
              omega
          have hk_val : n - 1 - lastZeroIdx w n = k.val := by rw [hm_eq]; omega
          have hk_eq : (⟨n - 1 - lastZeroIdx w n, by omega⟩ : Fin n) = k := Fin.ext hk_val
          have htake2 : (w.drop (lastZeroIdx w n + 1)).take (n - 1 - lastZeroIdx w n + 1) = w₂ := by
            rw [hm_eq, show n - 1 - (n - 1 - k.val) + 1 = k.val + 1 by omega]
            have hw_eq : w = (w₁ ++ [MotzkinStep.U]) ++ (w₂ ++ [MotzkinStep.D]) := by
              simp [w, List.append_assoc]
            have hlen_pre : (w₁ ++ [MotzkinStep.U]).length = n - 1 - k.val + 1 := by simp [hlen1]
            rw [hw_eq, ← hlen_pre, List.drop_left,
                List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
          have htake1 : w.take (lastZeroIdx w n) = w₁ := by
            rw [hm_eq]
            have hw_eq : w = w₁ ++ ([MotzkinStep.U] ++ w₂ ++ [MotzkinStep.D]) := by
              simp [w, List.append_assoc]
            rw [hw_eq, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
          refine sigma_prod_ext (P := fun j : Fin n => Exc (j.val + 1))
            (Q := fun j : Fin n => Exc (n - 1 - j.val)) hk_eq ?_ ?_
          · exact exc_heq (congrArg (· + 1) hk_val) htake2
          · exact exc_heq (congrArg (fun j => n - 1 - j) hk_val) htake1 }

private theorem a004148_recurrence (n : ℕ) :
    a004148 (n + 2) =
      a004148 (n + 1) + ∑ k ∈ Finset.range n, a004148 (k + 1) * a004148 (n - 1 - k) := by
  have : Finite (Exc (n + 1)) := finite_motzkin_len _ _
  have : ∀ k : Fin n, Finite (Exc (k.val + 1)) := fun _ => finite_motzkin_len _ _
  have : ∀ k : Fin n, Finite (Exc (n - 1 - k.val)) := fun _ => finite_motzkin_len _ _
  have : ∀ k : Fin n, Finite (Exc (k.val + 1) × Exc (n - 1 - k.val)) := fun _ => inferInstance
  have h := Nat.card_congr (excDecompEquiv n)
  rw [Nat.card_sum, Nat.card_sigma] at h
  simp only [Nat.card_prod] at h
  rw [Fin.sum_univ_eq_sum_range (fun k => Nat.card (Exc (k + 1)) * Nat.card (Exc (n - 1 - k)))] at h
  exact h

/-- Step 6 (Prefix decomposition): for every `n, k : ℕ`,
`PrefH (n + 1) (k + 1) ≃ Σ m : Fin (n + 1), Exc m.val × PrefH (n - m.val) k`. -/
private noncomputable def prefHDecompEquiv (n k : ℕ) :
    PrefH (n + 1) (k + 1) ≃ Σ m : Fin (n + 1), Exc m.val × PrefH (n - m.val) k := by
  refine
    { toFun := fun ⟨w, hlen, hpref, hk⟩ =>
        let m := lastZeroIdx w n
        have hm_le : m ≤ n := lastZeroIdx_le (by omega)
        have hm_zero : prefixHeight w m = 0 := prefixHeight_lastZeroIdx w n
        have hnonneg_n1 : ∀ i ≤ n + 1, 0 ≤ prefixHeight w i := fun i hi => hpref.1 i (by omega)
        have hmU : w[m]'(by omega) = MotzkinStep.U :=
          getElem_lastZeroIdx_eq_U (by omega) hnonneg_n1 (by omega)
        let w₁ : List MotzkinStep := w.take m
        let w₂ : List MotzkinStep := w.drop (m + 1)
        have hw_decomp : w = w₁ ++ [MotzkinStep.U] ++ w₂ := by
          have hmid := list_split_at_mid w (m := m) (by omega)
          rwa [hmU] at hmid
        have hw1_len : w₁.length = m := by simp [w₁, hlen]; omega
        have hw2_len : w₂.length = n - m := by simp [w₂, hlen]
        have hph1 : ∀ i ≤ m, prefixHeight w₁ i = prefixHeight w i := fun i hi => by
          conv_rhs => rw [hw_decomp, List.append_assoc]
          rw [prefixHeight_append_left w₁ _ (by omega)]
        have hph2 : ∀ r ≤ n - m, prefixHeight w (m + 1 + r) = 1 + prefixHeight w₂ r := fun r _ => by
          have hl : (w₁ ++ [MotzkinStep.U]).length = m + 1 := by simp [hw1_len]
          have hlp : prefixHeight (w₁ ++ [MotzkinStep.U]) (m + 1) = 1 := by
            rw [show m + 1 = w₁.length + 1 by omega, prefixHeight_append_right,
                hw1_len, hph1 m (le_refl m), hm_zero]
            rfl
          conv_lhs => rw [hw_decomp, ← hl]
          rw [prefixHeight_append_right, hl, hlp]
        ⟨⟨m, by omega⟩,
          ⟨w₁, hw1_len,
            ⟨fun i hi => by
                rw [hw1_len] at hi
                rw [hph1 i hi]
                exact hpref.1 i (by omega),
              isPeakless_take hpref.2 m⟩,
            by rw [hph1 m (le_refl m), hm_zero]⟩,
          ⟨w₂, hw2_len,
            ⟨fun r hr => by
                rw [hw2_len] at hr
                have h1 := one_le_prefixHeight_of_gt_lastZeroIdx hnonneg_n1
                  (i := m + 1 + r) (by omega) (by omega)
                rw [hph2 r hr] at h1
                omega,
              isPeakless_drop hpref.2 (m + 1)⟩,
            by
              dsimp only
              have h1 := hph2 (n - m) (le_refl _)
              have hidx : m + 1 + (n - m) = n + 1 := by omega
              rw [hidx, hk] at h1
              omega⟩⟩
      invFun := fun ⟨m, ⟨w₁, hlen1, hpref1, h01⟩, ⟨w₂, hlen2, hpref2, hk2⟩⟩ =>
        let w : List MotzkinStep := w₁ ++ [MotzkinStep.U] ++ w₂
        have hlen : w.length = n + 1 := by simp [w, hlen1, hlen2]; omega
        have hph_right : ∀ r ≤ n - m.val,
            prefixHeight w (m.val + 1 + r) = 1 + prefixHeight w₂ r := fun r _ => by
          have hl : (w₁ ++ [MotzkinStep.U]).length = m.val + 1 := by simp [hlen1]
          have hlp : prefixHeight (w₁ ++ [MotzkinStep.U]) (m.val + 1) = 1 := by
            rw [show m.val + 1 = w₁.length + 1 by omega, prefixHeight_append_right, hlen1, h01]
            rfl
          rw [show w = (w₁ ++ [MotzkinStep.U]) ++ w₂ from rfl, ← hl,
              prefixHeight_append_right, hl, hlp]
        ⟨w, hlen,
          ⟨fun i hi => by
              rw [hlen] at hi
              by_cases hi1 : i ≤ m.val
              · rw [show w = w₁ ++ ([MotzkinStep.U] ++ w₂) by simp [w, List.append_assoc],
                    prefixHeight_append_left w₁ _ (by omega)]
                exact hpref1.1 i (by omega)
              · have hr : i - (m.val + 1) ≤ n - m.val := by omega
                have heq : i = m.val + 1 + (i - (m.val + 1)) := by omega
                rw [heq, hph_right _ hr]
                have := hpref2.1 (i - (m.val + 1)) (by omega)
                omega,
            by
              have h1 : IsPeakless (w₁ ++ [MotzkinStep.U]) :=
                (isPeakless_append_iff w₁ [MotzkinStep.U]).mpr
                  ⟨hpref1.2, trivial, fun _ _ _ => by simp⟩
              refine (isPeakless_append_iff (w₁ ++ [MotzkinStep.U]) w₂).mpr
                ⟨h1, hpref2.2, fun _ hv _ => ?_⟩
              exact first_ne_D_of_prefix hpref2 hv⟩,
          by
            have heq : n + 1 = m.val + 1 + (n - m.val) := by omega
            rw [heq, hph_right (n - m.val) (le_refl _), hk2]
            omega⟩
      left_inv := by
        rintro ⟨w, hlen, hpref, hk⟩
        apply Subtype.ext
        dsimp only
        have hm_le : lastZeroIdx w n ≤ n := lastZeroIdx_le (by omega)
        have hnonneg_n1 : ∀ i ≤ n + 1, 0 ≤ prefixHeight w i := fun i hi => hpref.1 i (by omega)
        have hmU : w[lastZeroIdx w n]'(by omega) = MotzkinStep.U :=
          getElem_lastZeroIdx_eq_U (by omega) hnonneg_n1 (by omega)
        have hmid := list_split_at_mid w (m := lastZeroIdx w n) (by omega)
        rw [hmU] at hmid
        exact hmid.symm
      right_inv := by
        rintro ⟨m, ⟨w₁, hlen1, hpref1, h01⟩, ⟨w₂, hlen2, hpref2, hk2⟩⟩
        dsimp only
        let w : List MotzkinStep := w₁ ++ [MotzkinStep.U] ++ w₂
        have hm_eq : lastZeroIdx w n = m.val := by
          refine lastZeroIdx_eq (by omega) ?_ ?_
          · rw [show w = w₁ ++ ([MotzkinStep.U] ++ w₂) by simp [w, List.append_assoc],
                prefixHeight_append_left w₁ _ (by omega), h01]
          · intro i hgt hiN
            have hr : i - (m.val + 1) ≤ n - m.val := by omega
            have heq : i = m.val + 1 + (i - (m.val + 1)) := by omega
            have hl : (w₁ ++ [MotzkinStep.U]).length = m.val + 1 := by simp [hlen1]
            have hlp : prefixHeight (w₁ ++ [MotzkinStep.U]) (m.val + 1) = 1 := by
              rw [show m.val + 1 = w₁.length + 1 by omega, prefixHeight_append_right, hlen1, h01]
              rfl
            have hpos : prefixHeight w i = 1 + prefixHeight w₂ (i - (m.val + 1)) := by
              conv_lhs => rw [heq, show w = (w₁ ++ [MotzkinStep.U]) ++ w₂ from rfl, ← hl]
              rw [prefixHeight_append_right, hl, hlp]
            have := hpref2.1 (i - (m.val + 1)) (by omega)
            omega
        have hm_fin : (⟨lastZeroIdx w n, by omega⟩ : Fin (n + 1)) = m := Fin.ext hm_eq
        have htake1 : w.take (lastZeroIdx w n) = w₁ := by
          rw [hm_eq, show w = w₁ ++ ([MotzkinStep.U] ++ w₂) by simp [w, List.append_assoc],
              List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
        have hdrop2 : w.drop (lastZeroIdx w n + 1) = w₂ := by
          rw [hm_eq]
          have hl : (w₁ ++ [MotzkinStep.U]).length = m.val + 1 := by simp [hlen1]
          rw [show w = (w₁ ++ [MotzkinStep.U]) ++ w₂ from rfl, ← hl, List.drop_left]
        refine sigma_prod_ext (P := fun j : Fin (n + 1) => Exc j.val)
          (Q := fun j : Fin (n + 1) => PrefH (n - j.val) k) hm_fin ?_ ?_
        · exact exc_heq hm_eq htake1
        · exact prefH_heq (congrArg (fun j => n - j) hm_eq) hdrop2 }

private theorem a097724_col0 (n : ℕ) : a097724 n 0 = a004148 n := by
  rfl

private theorem a097724_zero_succ (k : ℕ) : a097724 0 (k + 1) = 0 := by
  unfold a097724
  have : IsEmpty (PrefH 0 (k + 1)) :=
    ⟨fun ⟨w, _, _, hk⟩ => by
      rw [prefixHeight_zero] at hk
      omega⟩
  exact Nat.card_of_isEmpty

private theorem a097724_succ_succ (n k : ℕ) :
    a097724 (n + 1) (k + 1) =
      ∑ m ∈ Finset.range (n + 1), a004148 m * a097724 (n - m) k := by
  have : ∀ m : Fin (n + 1), Finite (Exc m.val) := fun _ => finite_motzkin_len _ _
  have : ∀ m : Fin (n + 1), Finite (PrefH (n - m.val) k) := fun _ => finite_motzkin_len _ _
  have : ∀ m : Fin (n + 1), Finite (Exc m.val × PrefH (n - m.val) k) := fun _ => inferInstance
  have h := Nat.card_congr (prefHDecompEquiv n k)
  rw [Nat.card_sigma] at h
  simp only [Nat.card_prod] at h
  rw [Fin.sum_univ_eq_sum_range (fun m => Nat.card (Exc m) * Nat.card (PrefH (n - m) k))] at h
  exact h

private theorem a091964_eq_sum_a097724 (n : ℕ) :
    a091964 n = ∑ k ∈ Finset.range (n + 1), a097724 n k := by
  have : ∀ k : Fin (n + 1), Finite (PrefH n k.val) := fun _ => finite_motzkin_len _ _
  let e : Pref n ≃ Σ k : Fin (n + 1), PrefH n k.val :=
    { toFun := fun ⟨w, hlen, hpref⟩ =>
        have hlo : 0 ≤ prefixHeight w n := hpref.1 n (by omega)
        have hhi : prefixHeight w n ≤ (n : ℤ) := by
          simpa [hlen] using prefixHeight_le_length w
        ⟨⟨(prefixHeight w n).toNat, by omega⟩, ⟨w, hlen, hpref, by dsimp only; omega⟩⟩
      invFun := fun ⟨_, w, hlen, hpref, _⟩ => ⟨w, hlen, hpref⟩
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨⟨k, hk⟩, ⟨w, hlen, hpref, hkw⟩⟩ => by
        dsimp only
        have hkn : (prefixHeight w n).toNat = k := by
          dsimp only at hkw
          omega
        refine Sigma.ext (Fin.ext hkn) ?_
        exact subtype_heq (by simp [hkn]) rfl }
  have h := Nat.card_congr e
  rw [Nat.card_sigma] at h
  rw [Fin.sum_univ_eq_sum_range (fun k => Nat.card (PrefH n k))] at h
  exact h

/-! ### 6. Proof Section 3: Generating-Function Algebra in `PowerSeries ℕ` and `PowerSeries (Polynomial ℤ)` -/

/-- Ordinary generating function of `A004148` in `PowerSeries ℕ`. -/
private noncomputable def G_nat : PowerSeries ℕ :=
  PowerSeries.mk a004148

private theorem coeff_G_nat (n : ℕ) : PowerSeries.coeff n G_nat = a004148 n :=
  PowerSeries.coeff_mk n a004148

private theorem G_nat_quad :
    G_nat + PowerSeries.X ^ 2 * G_nat =
      1 + PowerSeries.X * G_nat + PowerSeries.X ^ 2 * G_nat ^ 2 := by
  refine PowerSeries.ext fun m => ?_
  match m with
  | 0 =>
    simp [G_nat, a004148_zero]
  | 1 =>
    simp [coeff_G_nat, a004148_zero, a004148_one, PowerSeries.coeff_X_pow_mul']
  | n + 2 =>
    have hX2 : PowerSeries.coeff (n + 2) (PowerSeries.X ^ 2 * G_nat) = a004148 n := by
      simp [coeff_G_nat]
    have hX1 : PowerSeries.coeff (n + 2) (PowerSeries.X * G_nat) = a004148 (n + 1) := by
      simp [coeff_G_nat]
    have hX2G2 : PowerSeries.coeff (n + 2) (PowerSeries.X ^ 2 * G_nat ^ 2) =
        ∑ j ∈ Finset.range (n + 1), a004148 j * a004148 (n - j) := by
      rw [PowerSeries.coeff_X_pow_mul, sq, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp [coeff_G_nat]
    have hsplit : ∑ j ∈ Finset.range (n + 1), a004148 j * a004148 (n - j) =
        a004148 n + ∑ k ∈ Finset.range n, a004148 (k + 1) * a004148 (n - 1 - k) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.sub_zero, a004148_zero, one_mul, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      have : n - (k + 1) = n - 1 - k := by omega
      rw [this]
    have h1 : PowerSeries.coeff (n + 2) (1 : PowerSeries ℕ) = 0 := by simp
    simp only [map_add, coeff_G_nat, hX2, h1, zero_add, hX1, hX2G2, hsplit, a004148_recurrence n]
    ring

private theorem a097724_eq_coeff_X_pow_mul_G_pow (k n : ℕ) :
    a097724 n k = PowerSeries.coeff n (PowerSeries.X ^ k * G_nat ^ (k + 1)) := by
  have hser : ∀ k : ℕ, PowerSeries.mk (fun n => a097724 n k) =
      PowerSeries.X ^ k * G_nat ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      refine PowerSeries.ext fun n => ?_
      simp [a097724_col0, coeff_G_nat]
    | succ k ih =>
      have hstep : PowerSeries.mk (fun n => a097724 n (k + 1)) =
          PowerSeries.X * (G_nat * PowerSeries.mk (fun n => a097724 n k)) := by
        refine PowerSeries.ext fun m => ?_
        cases m with
        | zero =>
          simp [a097724_zero_succ]
        | succ m =>
          rw [PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul,
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, a097724_succ_succ]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp [coeff_G_nat]
      rw [hstep, ih]
      ring
  have := congrArg (PowerSeries.coeff n) (hser k)
  simpa using this

private noncomputable abbrev pX : Polynomial ℤ := Polynomial.X
private noncomputable abbrev Z : PowerSeries (Polynomial ℤ) := PowerSeries.X

/-- Lift `G_nat` to `PowerSeries (Polynomial ℤ)`. -/
private noncomputable def G_poly : PowerSeries (Polynomial ℤ) :=
  PowerSeries.map (Nat.castRingHom (Polynomial ℤ)) G_nat

private theorem coeff_G_poly (n : ℕ) :
    PowerSeries.coeff n G_poly = (a004148 n : Polynomial ℤ) := by
  simp [G_poly, coeff_G_nat]

private theorem G_poly_quad :
    G_poly + Z ^ 2 * G_poly = 1 + Z * G_poly + Z ^ 2 * G_poly ^ 2 := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom (Polynomial ℤ))) G_nat_quad
  simpa [G_poly, Z, map_add, map_mul, map_pow, map_one] using h

private theorem coeff_Z_pow_mul_G_poly_pow (n k : ℕ) :
    PowerSeries.coeff n (Z ^ k * G_poly ^ (k + 1)) = (a097724 n k : Polynomial ℤ) := by
  have h : Z ^ k * G_poly ^ (k + 1) =
      PowerSeries.map (Nat.castRingHom (Polynomial ℤ)) (PowerSeries.X ^ k * G_nat ^ (k + 1)) := by
    simp [G_poly, Z, map_mul, map_pow]
  rw [h, PowerSeries.coeff_map, ← a097724_eq_coeff_X_pow_mul_G_pow]
  rfl

private theorem a097724_eq_zero_of_lt {n k : ℕ} (h : n < k) : a097724 n k = 0 := by
  rw [a097724_eq_coeff_X_pow_mul_G_pow, PowerSeries.coeff_X_pow_mul']
  simp [Nat.not_le.mpr h]

/-- Generating function `V(z) = ∑_{n≥0} u_n(X + 1) z^n ∈ (ℤ[X])⟦z⟧`. -/
private noncomputable def V_ser : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk (fun n => (uPoly n).comp (pX + 1))

private theorem V_ser_mul_denom :
    (1 - PowerSeries.C (pX + 1) * Z + Z ^ 2) * V_ser = 1 := by
  refine PowerSeries.ext fun m => ?_
  have hexp : (1 - PowerSeries.C (pX + 1) * Z + Z ^ 2) * V_ser =
      V_ser - PowerSeries.C (pX + 1) * (Z * V_ser) + Z ^ 2 * V_ser := by ring
  rw [hexp]
  match m with
  | 0 =>
    simp [V_ser, uPoly]
  | 1 =>
    rw [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_X_pow_mul']
    simp [V_ser, uPoly]
  | n + 2 =>
    have hZ2 : PowerSeries.coeff (n + 2) (Z ^ 2 * V_ser) = (uPoly n).comp (pX + 1) := by
      simp [V_ser]
    have hZ1 : PowerSeries.coeff (n + 2) (Z * V_ser) = (uPoly (n + 1)).comp (pX + 1) := by
      simp [V_ser]
    have h1 : PowerSeries.coeff (n + 2) (1 : PowerSeries (Polynomial ℤ)) = 0 := by simp
    rw [map_add, map_sub, PowerSeries.coeff_C_mul, hZ1, hZ2, h1, V_ser, PowerSeries.coeff_mk]
    simp [uPoly, Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.X_comp]

/-- Generating function `W(z) = ∑_{n≥0} (∑_{k=0}^n A097724(n, k) u_k(X)) z^n ∈ (ℤ[X])⟦z⟧`. -/
private noncomputable def W_ser : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk (fun n => ∑ k ∈ Finset.range (n + 1), (a097724 n k : Polynomial ℤ) * uPoly k)

private theorem coeff_W_ser_extend {m n : ℕ} (hmn : m ≤ n) :
    PowerSeries.coeff m W_ser =
      ∑ k ∈ Finset.range (n + 1), (a097724 m k : Polynomial ℤ) * uPoly k := by
  rw [W_ser, PowerSeries.coeff_mk]
  refine Finset.sum_subset (Finset.range_mono (by omega)) fun k _ hk => ?_
  have hmk : m < k := by
    simp only [Finset.mem_range] at hk
    omega
  simp [a097724_eq_zero_of_lt hmk]

private theorem coeff_ZG_pow_mul_W (d n : ℕ) :
    PowerSeries.coeff n ((Z * G_poly) ^ d * W_ser) =
      ∑ k ∈ Finset.range (n + 1), (a097724 n (k + d) : Polynomial ℤ) * uPoly k := by
  rw [PowerSeries.coeff_mul]
  have h1 : ∀ p ∈ Finset.antidiagonal n,
      PowerSeries.coeff p.1 ((Z * G_poly) ^ d) * PowerSeries.coeff p.2 W_ser =
      ∑ k ∈ Finset.range (n + 1),
        PowerSeries.coeff p.1 ((Z * G_poly) ^ d) *
          PowerSeries.coeff p.2 (Z ^ k * G_poly ^ (k + 1)) * uPoly k := by
    intro p hp
    have hp2 : p.2 ≤ n := by
      have := Finset.mem_antidiagonal.mp hp
      omega
    rw [coeff_W_ser_extend hp2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coeff_Z_pow_mul_G_poly_pow, mul_assoc]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_mul, ← PowerSeries.coeff_mul]
  have hpow : (Z * G_poly) ^ d * (Z ^ k * G_poly ^ (k + 1)) =
      Z ^ (k + d) * G_poly ^ (k + d + 1) := by ring
  rw [hpow, coeff_Z_pow_mul_G_poly_pow]

private theorem W_ser_quad_eq :
    (1 - PowerSeries.C pX * Z * G_poly + Z ^ 2 * G_poly ^ 2) * W_ser = G_poly := by
  refine PowerSeries.ext fun n => ?_
  have hexp : (1 - PowerSeries.C pX * Z * G_poly + Z ^ 2 * G_poly ^ 2) * W_ser =
      W_ser - PowerSeries.C pX * ((Z * G_poly) ^ 1 * W_ser) + (Z * G_poly) ^ 2 * W_ser := by
    ring
  rw [hexp, map_add, map_sub, PowerSeries.coeff_C_mul, coeff_ZG_pow_mul_W, coeff_ZG_pow_mul_W,
      coeff_G_poly]
  have hW : PowerSeries.coeff n W_ser =
      ∑ k ∈ Finset.range (n + 1), (a097724 n k : Polynomial ℤ) * uPoly k :=
    PowerSeries.coeff_mk n _
  rw [hW]
  have hr0 : (a097724 n 0 : Polynomial ℤ) = (a004148 n : Polynomial ℤ) := by
    rw [a097724_col0]
  rw [← hr0]
  match n with
  | 0 =>
    simp [uPoly, a097724_eq_zero_of_lt (show 0 < 1 by omega),
          a097724_eq_zero_of_lt (show 0 < 2 by omega)]
  | 1 =>
    simp [Finset.sum_range_succ, uPoly,
          a097724_eq_zero_of_lt (show 1 < 2 by omega),
          a097724_eq_zero_of_lt (show 1 < 3 by omega)]
    ring
  | m + 2 =>
    have hS0 : ∑ k ∈ Finset.range (m + 3), (a097724 (m + 2) k : Polynomial ℤ) * uPoly k =
        (a097724 (m + 2) 0 : Polynomial ℤ) * uPoly 0 +
        (a097724 (m + 2) 1 : Polynomial ℤ) * uPoly 1 +
        ∑ k ∈ Finset.range (m + 1), (a097724 (m + 2) (k + 2) : Polynomial ℤ) * uPoly (k + 2) := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      ring
    have hS1 : ∑ k ∈ Finset.range (m + 3), (a097724 (m + 2) (k + 1) : Polynomial ℤ) * uPoly k =
        (a097724 (m + 2) 1 : Polynomial ℤ) * uPoly 0 +
        ∑ k ∈ Finset.range (m + 1), (a097724 (m + 2) (k + 2) : Polynomial ℤ) * uPoly (k + 1) := by
      rw [Finset.sum_range_succ, a097724_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, add_zero]
      rw [Finset.sum_range_succ']
      ring
    have hS2 : ∑ k ∈ Finset.range (m + 3), (a097724 (m + 2) (k + 2) : Polynomial ℤ) * uPoly k =
        ∑ k ∈ Finset.range (m + 1), (a097724 (m + 2) (k + 2) : Polynomial ℤ) * uPoly k := by
      rw [Finset.sum_range_succ, a097724_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, add_zero]
      rw [Finset.sum_range_succ, a097724_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, add_zero]
    rw [hS0, hS1, hS2, mul_add, Finset.mul_sum]
    have htel :
        (∑ k ∈ Finset.range (m + 1), (a097724 (m + 2) (k + 2) : Polynomial ℤ) * uPoly (k + 2)) -
        (∑ k ∈ Finset.range (m + 1), pX * ((a097724 (m + 2) (k + 2) : Polynomial ℤ) * uPoly (k + 1))) +
        (∑ k ∈ Finset.range (m + 1), (a097724 (m + 2) (k + 2) : Polynomial ℤ) * uPoly k) = 0 := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun k _ => ?_
      simp only [uPoly, pX]
      ring
    have hu01 : (a097724 (m + 2) 0 : Polynomial ℤ) * uPoly 0 +
        (a097724 (m + 2) 1 : Polynomial ℤ) * uPoly 1 -
        pX * ((a097724 (m + 2) 1 : Polynomial ℤ) * uPoly 0) =
        (a097724 (m + 2) 0 : Polynomial ℤ) := by
      simp only [uPoly, pX]
      ring
    linear_combination hu01 + htel

private theorem W_ser_eq_V_ser : W_ser = V_ser := by
  have hfac : 1 - PowerSeries.C pX * Z * G_poly + Z ^ 2 * G_poly ^ 2 =
      (1 - PowerSeries.C (pX + 1) * Z + Z ^ 2) * G_poly := by
    have hC : PowerSeries.C (pX + 1) = PowerSeries.C pX + 1 := by
      rw [map_add, map_one]
    rw [hC]
    linear_combination -G_poly_quad
  have hmul : (1 - PowerSeries.C (pX + 1) * Z + Z ^ 2) * W_ser * G_poly = 1 * G_poly := by
    calc (1 - PowerSeries.C (pX + 1) * Z + Z ^ 2) * W_ser * G_poly
        = (1 - PowerSeries.C (pX + 1) * Z + Z ^ 2) * G_poly * W_ser := by ring
      _ = (1 - PowerSeries.C pX * Z * G_poly + Z ^ 2 * G_poly ^ 2) * W_ser := by rw [← hfac]
      _ = G_poly := W_ser_quad_eq
      _ = 1 * G_poly := by rw [one_mul]
  have hG_unit : IsUnit G_poly := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have : PowerSeries.constantCoeff G_poly = 1 := by
      simpa [a004148_zero] using coeff_G_poly 0
    rw [this]
    exact isUnit_one
  have hW_inv : (1 - PowerSeries.C (pX + 1) * Z + Z ^ 2) * W_ser = 1 :=
    hG_unit.mul_right_cancel hmul
  have hD_unit : IsUnit (1 - PowerSeries.C (pX + 1) * Z + Z ^ 2) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp [Z]
  exact hD_unit.mul_left_cancel (hW_inv.trans V_ser_mul_denom.symm)

private theorem isA191579Row_a097724 (n : ℕ) : IsA191579Row n (a097724 n) := by
  refine ⟨fun k hk => a097724_eq_zero_of_lt hk, fun j => ?_⟩
  have hcoeff := congrArg (PowerSeries.coeff n) W_ser_eq_V_ser
  simp only [W_ser, V_ser, PowerSeries.coeff_mk] at hcoeff
  have heval := congrArg (fun p : Polynomial ℤ => p.eval ((j : ℤ) + 2)) hcoeff
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_natCast,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] at heval
  have hlhs : (uPoly n).eval ((j : ℤ) + 2 + 1) = (a192062 (2 * n + 2) (j + 1) : ℤ) := by
    rw [a192062_even_eq_uPoly n (j + 1)]
    push_cast
    ring_nf
  have hrhs :
      (∑ k ∈ Finset.range (n + 1), (a097724 n k : ℤ) * (uPoly k).eval ((j : ℤ) + 2)) =
      ((∑ k ∈ Finset.range (n + 1), a097724 n k * a192062 (2 * k + 2) j : ℕ) : ℤ) := by
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [a192062_even_eq_uPoly k j]
  rw [hlhs, hrhs] at heval
  exact_mod_cast heval.symm

/-- Full triangle equality (`OEIS A191579 = OEIS A097724` in 0-based indexing). -/
theorem a191579_eq_a097724 (n k : ℕ) : a191579 n k = a097724 n k := by
  have hex : ∃ r : ℕ → ℕ, IsA191579Row n r := ⟨a097724 n, isA191579Row_a097724 n⟩
  have hspec : IsA191579Row n (Classical.epsilon (IsA191579Row n)) :=
    Classical.epsilon_spec hex
  have hrow : Classical.epsilon (IsA191579Row n) = a097724 n :=
    isA191579Row_unique hspec (isA191579Row_a097724 n)
  exact congrFun hrow k

/-! ### 7. Pinned Theorems (Well-Definedness + Four-Claim C042 Bundle) -/

theorem a191579_row_exists_unique (n : ℕ) :
    ∃! r : ℕ → ℕ, IsA191579Row n r :=
  ⟨a097724 n, isA191579Row_a097724 n, fun _ hr => isA191579Row_unique hr (isA191579Row_a097724 n)⟩

theorem a191579_rowSum_eq_a091964 (n : ℕ) :
    a191579RowSum n = a091964 n := by
  unfold a191579RowSum
  rw [a091964_eq_sum_a097724]
  refine Finset.sum_congr rfl fun k _ => a191579_eq_a097724 n k

theorem a191579_col0_eq_a004148 (n : ℕ) :
    a191579Col 0 n = a004148 n := by
  unfold a191579Col
  rw [a191579_eq_a097724, a097724_col0]

theorem a191579_col1_eq_a089735 (n : ℕ) (hn : 1 ≤ n) :
    a191579Col 1 n = a089735 (n - 1) := by
  unfold a191579Col a089735
  rw [a191579_eq_a097724, a097724_eq_coeff_X_pow_mul_G_pow]
  have hn' : n = (n - 1) + 1 := by omega
  conv_lhs => rw [hn']
  rw [pow_one, PowerSeries.coeff_succ_X_mul, sq, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [coeff_G_nat]

theorem a191579_col2_eq_a098075 (n : ℕ) (hn : 2 ≤ n) :
    a191579Col 2 n = a098075 (n - 2) := by
  unfold a191579Col a098075
  rw [a191579_eq_a097724, a097724_eq_coeff_X_pow_mul_G_pow]
  have hn' : n = (n - 2) + 2 := by omega
  conv_lhs => rw [hn']
  rw [PowerSeries.coeff_X_pow_mul, show G_nat ^ (2 + 1) = G_nat * (G_nat * G_nat) by ring,
      PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_G_nat, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [coeff_G_nat, mul_assoc]

end MathProofs.SeamB.C042
