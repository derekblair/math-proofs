import Mathlib
import Mathproofs.CollatzGapC29

/-!
# C29′: from-below mirror of C29 (R99)

Source: `~/workspace/math-unsolved/ROUND99_DOSSIER.md` (Round 99, [PROVED*]).

**Theorem (C29′).** Let `α ∉ ℚ` and `Q ≥ 1` be a strict from-below record:
`f(Q) < f(q)` for all `1 ≤ q < Q`, where `f(q) = α − ⌊qα⌋/q`. Then
`#{x < Q : {xα} > s} ≥ Q(1−s) − 1` for all `s ∈ [0,1]`.

Proof: the `β = m − α` transfer with integer `m = ⌊α⌋ + 1`, so
`β ∈ (0,1)` is irrational and positive (the Lean `c29` needs `0 < α`,
so the bare `−α` of the hand proof is shifted by an integer — the
record and fract identities are unaffected). `e_β(q) = f(q)`
definitionally (`⌈−y⌉ = −⌊y⌋` for `y ∉ ℤ`), so `IsStrictRecord β Q`
holds and C29 (`CollatzGapC29.c29`) applies to `β`. `{xβ} = 1 − {xα}`
for `x ≥ 1` (and `0` at `x = 0`); the counting rearrangement
`#{x<Q : {xβ} < t} = 1 + #{x<Q : {xα} > 1−t}` (for `0 < t ≤ 1`) turns
C29's `Q·t ≤ #{…}` into the mirror bound — the `−1` is exactly the
`x = 0` correction.
-/

namespace CollatzGapC29Mirror

open Finset

/-- From-below approximation error `f(q) = α − ⌊qα⌋/q`. -/
noncomputable def approxErrBelow (α : ℝ) (q : ℕ) : ℝ :=
  α - (⌊(q : ℝ) * α⌋ : ℝ) / q

/-- Strict from-below record: `Q` beats every smaller positive denominator. -/
def IsStrictBelowRecord (α : ℝ) (Q : ℕ) : Prop :=
  ∀ q : ℕ, 1 ≤ q → q < Q → approxErrBelow α Q < approxErrBelow α q

variable {α : ℝ} {Q : ℕ}

/-- `y_x = {xα}`, the fractional-part sequence (keeps `x : ℕ` so the
`filter` predicates elaborate over `Finset ℕ`). -/
private noncomputable def yfrac (α : ℝ) : ℕ → ℝ := fun x => Int.fract ((x : ℝ) * α)

@[simp] private theorem yfrac_zero (α : ℝ) : yfrac α 0 = 0 := by simp [yfrac]

/-- Shift integer `m := ⌊α⌋ + 1`, so that `β = m − α ∈ (0,1)`. -/
private noncomputable def shiftInt (α : ℝ) : ℤ := ⌊α⌋ + 1

/-- The transferred parameter `β = m − α`. -/
private noncomputable def beta (α : ℝ) : ℝ := (shiftInt α : ℝ) - α

/-- `(q:ℝ) * α` is never an integer for `q ≥ 1` (irrationality of `α`). -/
private theorem mul_irr_ne_int (hα : Irrational α) (q : ℕ) (hq : 1 ≤ q) (k : ℤ) :
    (q : ℝ) * α ≠ (k : ℝ) := by
  intro h
  have hq0 : (q:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (lt_of_lt_of_le zero_lt_one hq)
  apply hα
  refine ⟨(k : ℚ) / (q : ℚ), ?_⟩
  have h1 : α = (k : ℝ) / (q : ℝ) := by
    rw [eq_div_iff hq0]
    linarith [h]
  rw [h1]
  norm_cast

/-- `β > 0`. -/
theorem beta_pos : 0 < beta α := by
  have h := Int.lt_floor_add_one α
  simp only [beta, shiftInt] at ⊢
  push_cast at h ⊢
  linarith

/-- `β` is irrational. -/
theorem beta_irr (hα : Irrational α) : Irrational (beta α) := by
  rw [irrational_iff_ne_rational] at hα ⊢
  intro a b hb hab
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have h1 : α = (shiftInt α : ℝ) - beta α := by
    simp only [beta]; ring
  have heq : ((b * shiftInt α - a : ℤ) : ℝ) / (b : ℝ)
      = (shiftInt α : ℝ) - (a : ℝ) / (b : ℝ) := by
    have h2 : ((b * shiftInt α - a : ℤ) : ℝ) = (b : ℝ) * (shiftInt α : ℝ) - (a : ℝ) := by
      push_cast; ring
    rw [h2, sub_div, mul_div_cancel_left₀ _ hbR]
  apply hα (b * shiftInt α - a) b hb
  rw [heq, ← hab, ← h1]

/-- `⌈qβ⌉ = −⌊qα⌋ + q·m` (the record correspondence at the ceiling level). -/
private theorem ceil_beta_eq (q : ℕ) :
    ⌈(q:ℝ) * beta α⌉ = -⌊(q:ℝ) * α⌋ + (q:ℤ) * shiftInt α := by
  have h1 : (q:ℝ) * beta α = -((q:ℝ) * α) + (((q:ℤ) * shiftInt α : ℤ) : ℝ) := by
    simp only [beta]
    push_cast
    ring
  rw [h1, Int.ceil_add_intCast, Int.ceil_neg]

/-- Record correspondence: `e_β(q) = f(q)` for `q ≥ 1` (definitional transfer). -/
theorem approxErr_beta_eq (q : ℕ) (hq : 1 ≤ q) :
    CollatzGapC29.approxErr (beta α) q = approxErrBelow α q := by
  have hq0 : (q:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (lt_of_lt_of_le zero_lt_one hq)
  have h2 := ceil_beta_eq (α := α) q
  simp only [CollatzGapC29.approxErr, approxErrBelow]
  rw [h2]
  simp only [beta]
  push_cast
  field_simp
  ring

/-- A from-below record of `α` is a from-above record of `β`. -/
theorem isStrictRecord_beta (hQ : 1 ≤ Q)
    (hrec : IsStrictBelowRecord α Q) :
    CollatzGapC29.IsStrictRecord (beta α) Q := by
  intro q h1 hlt
  rw [approxErr_beta_eq q h1, approxErr_beta_eq Q hQ]
  exact hrec q h1 hlt

/-- `fract(−y) = 1 − fract(y)` for `y ∉ ℤ`. -/
private theorem fract_neg_of_not_int {y : ℝ} (hy : ∀ k : ℤ, y ≠ (k:ℝ)) :
    Int.fract (-y) = 1 - Int.fract y := by
  have h1 : (⌊y⌋:ℝ) < y :=
    lt_of_le_of_ne (Int.floor_le y) (fun h => hy ⌊y⌋ h.symm)
  have hfloor : ⌊-y⌋ = -⌊y⌋ - 1 := by
    rw [Int.floor_eq_iff]
    constructor <;> push_cast <;> linarith [Int.lt_floor_add_one y, h1]
  have h2 : Int.fract (-y) = -y - ((-⌊y⌋ - 1 : ℤ):ℝ) := by
    rw [show Int.fract (-y) = -y - ((⌊-y⌋ : ℤ):ℝ) from rfl, hfloor]
  have h3 : Int.fract y = y - ((⌊y⌋ : ℤ):ℝ) := rfl
  rw [h2, h3]
  push_cast
  ring

/-- Fractional-part identity: `{xβ} = 1 − {xα}` for `x ≥ 1`. -/
theorem fract_beta_eq (hα : Irrational α) (x : ℕ) (hx : 1 ≤ x) :
    yfrac (beta α) x = 1 - yfrac α x := by
  have h2 : yfrac (beta α) x = Int.fract (-((x:ℝ) * α)) := by
    have h1 : (x:ℝ) * beta α = -((x:ℝ) * α) + (((x:ℤ) * shiftInt α : ℤ) : ℝ) := by
      simp only [beta]
      push_cast
      ring
    simp only [yfrac]
    rw [h1]
    exact Int.fract_add_intCast _ _
  rw [h2]
  have h3 : Int.fract ((x:ℝ) * α) = yfrac α x := by simp only [yfrac]
  rw [← h3]
  exact fract_neg_of_not_int (fun k => mul_irr_ne_int hα x hx k)

/-- Counting rearrangement: `#{x<Q : {xβ} < t} = 1 + #{x<Q : {xα} > 1−t}`
for `0 < t ≤ 1` (the `1` is the `x = 0` term). -/
theorem card_count (hα : Irrational α) (hQ : 1 ≤ Q) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ((range Q).filter (fun x => yfrac (beta α) x < t)).card
      = 1 + ((range Q).filter (fun x => 1 - t < yfrac α x)).card := by
  have hnot : (0:ℕ) ∉ (range Q).filter (fun x => 1 - t < yfrac α x) := by
    simp only [mem_filter, not_and]
    intro _ hlt
    rw [yfrac_zero] at hlt
    linarith
  have hset : (range Q).filter (fun x => yfrac (beta α) x < t)
      = insert 0 ((range Q).filter (fun x => 1 - t < yfrac α x)) := by
    ext x
    simp only [mem_filter, mem_range, mem_insert]
    constructor
    · rintro ⟨hxQ, hlt⟩
      rcases Nat.eq_zero_or_pos x with rfl | hxpos
      · exact Or.inl rfl
      · refine Or.inr ⟨hxQ, ?_⟩
        have hx1 : 1 ≤ x := hxpos
        rw [fract_beta_eq hα x hx1] at hlt
        have hfx0 : 0 < yfrac α x := by
          have h1 : (⌊(x:ℝ)*α⌋:ℝ) < (x:ℝ)*α :=
            lt_of_le_of_ne (Int.floor_le _) (fun h => mul_irr_ne_int hα x hx1 ⌊(x:ℝ)*α⌋ h.symm)
          have h2 : yfrac α x = (x:ℝ)*α - (⌊(x:ℝ)*α⌋:ℝ) := rfl
          linarith
        linarith
    · rintro (rfl | ⟨hxQ, hlt⟩)
      · refine ⟨by omega, ?_⟩
        rw [yfrac_zero]
        exact ht0
      · have hx1 : 1 ≤ x := by
          rcases Nat.eq_zero_or_pos x with rfl | h
          · exfalso
            rw [yfrac_zero] at hlt
            linarith
          · exact h
        refine ⟨hxQ, ?_⟩
        rw [fract_beta_eq hα x hx1]
        have hfx1 : yfrac α x < 1 := by
          have h2 : yfrac α x = Int.fract ((x:ℝ)*α) := by simp only [yfrac]
          rw [h2]
          exact Int.fract_lt_one _
        linarith
  rw [hset, Finset.card_insert_of_notMem hnot, Nat.add_comm]

/-- C29′ (R99): from-below discrepancy mirror of C29. -/
theorem c29_mirror (hα : Irrational α) (hQ : 1 ≤ Q)
    (hrec : IsStrictBelowRecord α Q) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (Q:ℝ) * (1 - s) - 1 ≤ ((((range Q).filter (fun x => s < yfrac α x)).card : ℕ):ℝ) := by
  rcases eq_or_lt_of_le hs1 with rfl | hslt
  · have hnn : (0:ℝ) ≤ ((((range Q).filter (fun x => (1:ℝ) < yfrac α x)).card : ℕ):ℝ) :=
      Nat.cast_nonneg _
    have h1 : (Q:ℝ) * (1 - 1) - 1 = -1 := by ring
    linarith
  · have ht0 : (0:ℝ) < 1 - s := by linarith
    have ht1 : (1:ℝ) - s ≤ 1 := by linarith
    have hc29 := CollatzGapC29.c29 (beta_irr hα) beta_pos hQ
      (isStrictRecord_beta hQ hrec) (1 - s) ht0.le ht1
    -- `c29` is stated with `CollatzGapC29`'s private `yfrac`; it is
    -- definitionally equal to ours, so convert by defeq.
    have hc29' : (Q:ℝ) * (1 - s)
        ≤ ((((range Q).filter (fun x => yfrac (beta α) x < 1 - s)).card : ℕ):ℝ) := hc29
    rw [card_count hα hQ (1 - s) ht0 ht1] at hc29'
    have hs_eq : (1:ℝ) - (1 - s) = s := by ring
    rw [hs_eq] at hc29'
    push_cast at hc29'
    linarith

end CollatzGapC29Mirror
