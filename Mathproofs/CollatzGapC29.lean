import Mathlib

/-!
# C29: one-sided Kronecker discrepancy dominance at strict from-above records (R52)

Source: `~/workspace/math-unsolved/ROUND52_DOSSIER.md` (Round 52).

**Theorem (C29).** Let `α ∉ ℚ`, `α > 0`. Let `Q ≥ 1` be a *strict* from-above
record: `e(Q) < e(q)` for all `1 ≤ q < Q`, where `e(q) = ⌈qα⌉/q - α`.
Then `D_Q(t) := #{x < Q : {xα} < t} - Q·t ≥ 0` for all `t ∈ [0,1]`
(in fact `> 0` on `(0,1)`).

Proof (R52): put `p α Q = ⌈Qα⌉`, `ε = p α Q - Qα ∈ (0,1)`.
* Lemma A: `gcd(p α Q,Q) = 1` (else `Q/d` is an as-good approximant).
* Lemma B (no wraps): `(px mod Q) ≥ xε` for all `1 ≤ x < Q` — a wrap would
  exhibit `⌊px/Q⌋/x`, a strictly better from-above approximant.
* Hence `{xα} = ((px mod Q) - xε)/Q`, and `x ↦ px mod Q` permutes
  `range Q`, so `#{x : y_x ≤ j/Q} ≥ j+1`; the discrepancy bound follows
  with `j = ⌊Qt⌋`.

Corollary C9(a) (`d(Q) > 0` at from-above upper-best `Q` of `log₂3`) follows
via R40's Abel identity `Q·d(Q) = ln2·∫₀¹D_Q(t)2^{-t}dt` ([PROVED] by hand in
R40; the integral step is out of scope this round, so C9(a) stays [PROVED*]).
-/

namespace CollatzGapC29

open Finset

/-- From-above approximation error `e(q) = ⌈qα⌉/q - α`. -/
noncomputable def approxErr (α : ℝ) (q : ℕ) : ℝ :=
  (⌈(q : ℝ) * α⌉ : ℝ) / q - α

/-- Strict from-above record: `Q` beats every smaller positive denominator. -/
def IsStrictRecord (α : ℝ) (Q : ℕ) : Prop :=
  ∀ q : ℕ, 1 ≤ q → q < Q → approxErr α Q < approxErr α q

variable {α : ℝ} {Q : ℕ}

/-- `p α Q = ⌈Qα⌉` as an integer. -/
private noncomputable def p (α : ℝ) (Q : ℕ) : ℤ := ⌈(Q : ℝ) * α⌉
/-- `P α Q`, the natural form of `p α Q` (nonneg since `Qα > 0`). -/
private noncomputable def P (α : ℝ) (Q : ℕ) : ℕ := (p α Q).toNat
/-- `ε = p α Q - Qα`, the fractional excess. -/
private noncomputable def eps (α : ℝ) (Q : ℕ) : ℝ := (P α Q : ℝ) - (Q : ℝ) * α
/-- `y_x = {xα}`, the fractional-part sequence. -/
private noncomputable def yfrac (α : ℝ) : ℕ → ℝ := fun x => Int.fract ((x : ℝ) * α)

private theorem hQ0 (hα : Irrational α) (hα0 : 0 < α) (hQ : 1 ≤ Q) : (0:ℝ) < (Q:ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_one hQ

/-- `q * α` is never an integer for `q ≥ 1` (irrationality of `α`). -/
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

private theorem hp_nonneg (hα : Irrational α) (hα0 : 0 < α) (hQ : 1 ≤ Q) : 0 ≤ p α Q := by
  have hpos : (0:ℝ) ≤ (Q:ℝ) * α := le_of_lt (mul_pos (hQ0 hα hα0 hQ) hα0)
  have h2 : (0:ℤ) ≤ ⌈(Q:ℝ) * α⌉ := Int.ceil_nonneg hpos
  simpa [p] using h2

private theorem hP_eq (hα : Irrational α) (hα0 : 0 < α) (hQ : 1 ≤ Q) : ((P α Q : ℕ) : ℤ) = p α Q :=
  Int.toNat_of_nonneg (hp_nonneg hα hα0 hQ)

private theorem hP_cast (hα : Irrational α) (hα0 : 0 < α) (hQ : 1 ≤ Q) : ((P α Q : ℕ) : ℝ) = (p α Q : ℝ) := by
  rw [← Int.cast_natCast, hP_eq hα hα0 hQ]

/-- `ε > 0`: `Qα ∉ ℤ` forces `Qα < ⌈Qα⌉`. -/
private theorem eps_pos (hα : Irrational α) (hα0 : 0 < α) (hQ : 1 ≤ Q) : 0 < eps α Q := by
  have hlt : (Q:ℝ) * α < (p α Q : ℝ) := by
    by_contra hle
    push Not at hle
    have hpeq : (p α Q : ℝ) = (⌈(Q:ℝ) * α⌉ : ℝ) := by simp only [p]
    rw [hpeq] at hle
    have heq : (Q:ℝ) * α = (⌈(Q:ℝ) * α⌉ : ℝ) :=
      le_antisymm (Int.le_ceil _) hle
    exact mul_irr_ne_int hα Q hQ ⌈(Q:ℝ) * α⌉ heq
  have hcast := hP_cast hα hα0 hQ
  simp only [eps]
  linarith

/-- `ε < 1` (ceiling property). -/
private theorem eps_lt_one (hα : Irrational α) (hα0 : 0 < α) (hQ : 1 ≤ Q) : eps α Q < 1 := by
  have h1 : (p α Q : ℝ) < (Q:ℝ) * α + 1 := Int.ceil_lt_add_one _
  have hcast := hP_cast hα hα0 hQ
  simp only [eps]
  linarith

/-- `e(Q) = P α Q/Q - α` (the ceiling is exactly `P α Q`). -/
private theorem approxErr_Q (hα : Irrational α) (hα0 : 0 < α) (hQ : 1 ≤ Q) : approxErr α Q = (P α Q : ℝ) / (Q:ℝ) - α := by
  have h1 : (⌈(Q:ℝ) * α⌉ : ℝ) = (P α Q : ℝ) := by
    have h2 : (⌈(Q:ℝ) * α⌉ : ℝ) = (p α Q : ℝ) := by simp only [p]
    rw [h2]
    exact (hP_cast hα hα0 hQ).symm
  simp only [approxErr]
  rw [h1]

/-! ## Lemma A: `gcd(P α Q, Q) = 1` -/

/-- Lemma A (R52): the strict-record property forces `gcd(⌈Qα⌉, Q) = 1`. -/
theorem lemmaA_coprime (hα : Irrational α) (hα0 : 0 < α) (hQ : 1 ≤ Q) (hrec : IsStrictRecord α Q) : Nat.Coprime (P α Q) Q := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  have hge : 2 ≤ Nat.gcd (P α Q) Q := by
    have hne0 : Nat.gcd (P α Q) Q ≠ 0 := by
      intro hz
      have hdvd := Nat.gcd_dvd_right (P α Q) Q
      rw [hz] at hdvd
      have h0 := (zero_dvd_iff.mp hdvd)
      omega
    omega
  obtain ⟨P', hP'⟩ := Nat.gcd_dvd_left (P α Q) Q
  obtain ⟨Q', hQ'⟩ := Nat.gcd_dvd_right (P α Q) Q
  have hQ'1 : 1 ≤ Q' := by
    rcases Nat.eq_zero_or_pos Q' with h | h
    · exfalso
      have hQ0' : Q = 0 := by
        have e : Q = Nat.gcd (P α Q) Q * Q' := hQ'
        rw [h] at e
        simpa using e
      omega
    · exact h
  have hQ'lt : Q' < Q := by
    have h1d : 1 < Nat.gcd (P α Q) Q := by omega
    have e : Q = Nat.gcd (P α Q) Q * Q' := hQ'
    calc Q' = 1 * Q' := (one_mul _).symm
      _ < Nat.gcd (P α Q) Q * Q' := by nlinarith [h1d, hQ'1]
      _ = Q := e.symm
  have hP'1 : 1 ≤ P' := by
    rcases Nat.eq_zero_or_pos P' with h | h
    · exfalso
      have hP0 : P α Q = 0 := by
        have e : P α Q = Nat.gcd (P α Q) Q * P' := hP'
        rw [h] at e
        simpa using e
      have hle0 : p α Q ≤ 0 := by
        have hPt : (p α Q).toNat = 0 := by
          have hPP : (p α Q).toNat = P α Q := rfl
          rw [hPP, hP0]
        exact Int.toNat_eq_zero.mp hPt
      have hpos : (0:ℝ) < (Q:ℝ) * α := mul_pos (hQ0 hα hα0 hQ) hα0
      have hle2 : (p α Q : ℝ) ≤ 0 := by exact_mod_cast hle0
      have hpeq : (p α Q : ℝ) = (⌈(Q:ℝ) * α⌉ : ℝ) := rfl
      linarith [Int.le_ceil ((Q:ℝ) * α), hpos, hle2, hpeq]
    · exact h
  have hratio : (P' : ℝ) / (Q':ℝ) = (P α Q : ℝ) / (Q:ℝ) := by
    have e1 : (P α Q : ℝ) = (P' : ℝ) * (Nat.gcd (P α Q) Q : ℝ) := by
      conv_lhs => rw [hP']
      push_cast; ring
    have e2 : (Q : ℝ) = (Q' : ℝ) * (Nat.gcd (P α Q) Q : ℝ) := by
      conv_lhs => rw [hQ']
      push_cast; ring
    have hQ'0 : (Q':ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (lt_of_lt_of_le zero_lt_one hQ'1)
    have hd0 : (Nat.gcd (P α Q) Q : ℝ) ≠ 0 := by
      exact_mod_cast ne_of_gt (lt_of_lt_of_le (by omega) hge)
    rw [e1, e2]
    field_simp
  have hge' : (Q' : ℝ) * α ≤ (P' : ℝ) := by
    have hPQ : (Q : ℝ) * α ≤ (P α Q : ℝ) := by
      have hcast := hP_cast hα hα0 hQ
      have hle : (Q:ℝ) * α ≤ (p α Q : ℝ) := Int.le_ceil _
      linarith
    have hd0 : (0:ℝ) < (Nat.gcd (P α Q) Q : ℝ) := by
      exact_mod_cast lt_of_lt_of_le (by omega) hge
    have e : Q = Nat.gcd (P α Q) Q * Q' := hQ'
    have eP : P α Q = Nat.gcd (P α Q) Q * P' := hP'
    have h1 : (Nat.gcd (P α Q) Q : ℝ) * ((Q':ℝ) * α)
        ≤ (Nat.gcd (P α Q) Q : ℝ) * (P':ℝ) := by
      have eR : (Q:ℝ) = (Nat.gcd (P α Q) Q : ℝ) * (Q':ℝ) := by exact_mod_cast e
      have ePR : (P α Q : ℝ) = (Nat.gcd (P α Q) Q : ℝ) * (P':ℝ) := by
        exact_mod_cast eP
      have key : (Nat.gcd (P α Q) Q : ℝ) * ((Q':ℝ) * α)
          = ((Nat.gcd (P α Q) Q : ℝ) * (Q':ℝ)) * α := by ring
      rw [key, ← eR, ← ePR]
      exact hPQ
    exact le_of_mul_le_mul_left h1 hd0
  have hle : approxErr α Q' ≤ approxErr α Q := by
    have hceil : (⌈(Q' : ℝ) * α⌉ : ℤ) ≤ (P' : ℤ) :=
      Int.ceil_le.mpr (by exact_mod_cast hge')
    have hceilR : (⌈(Q' : ℝ) * α⌉ : ℝ) ≤ (P' : ℝ) := by exact_mod_cast hceil
    have hQ'0 : (0:ℝ) < Q' := by exact_mod_cast lt_of_lt_of_le zero_lt_one hQ'1
    have h1 : (⌈(Q' : ℝ) * α⌉ : ℝ) / (Q':ℝ) ≤ (P' : ℝ) / (Q':ℝ) :=
      (div_le_div_iff_of_pos_right hQ'0).mpr hceilR
    have h2 : approxErr α Q' ≤ (P':ℝ)/(Q':ℝ) - α := by
      simp only [approxErr]
      linarith [h1]
    rw [hratio] at h2
    have hAQ := approxErr_Q hα hα0 hQ
    rw [hAQ] at ⊢
    linarith [h2]
  have hlt := hrec Q' hQ'1 hQ'lt
  linarith
/-! ## Lemma B: no wraps -/

/-- Lemma B (R52): no wraps — `(P α Q*x) % Q ≥ x*ε` for `1 ≤ x < Q`.
A wrap would exhibit `⌊px/Q⌋/x`, a strictly better from-above approximant. -/
theorem lemmaB_nowrap (hα : Irrational α) (hα0 : 0 < α) (hQ : 1 ≤ Q) (hrec : IsStrictRecord α Q) (x : ℕ) (hx1 : 1 ≤ x) (hxQ : x < Q) :
    (((P α Q * x) % Q : ℕ):ℝ) ≥ (x : ℝ) * eps α Q := by
  by_contra hlt
  push Not at hlt
  have hdm : Q * ((P α Q * x) / Q) + (P α Q * x) % Q
      = P α Q * x := Nat.div_add_mod _ _
  have hdmR : (Q:ℝ) * (((P α Q * x) / Q : ℕ):ℝ) + (((P α Q * x) % Q : ℕ):ℝ)
      = (P α Q : ℝ) * (x:ℝ) := by
    have h1 : ((Q * ((P α Q * x) / Q) + (P α Q * x) % Q : ℕ):ℝ)
        = ((P α Q * x : ℕ):ℝ) := by exact_mod_cast hdm
    push_cast at h1 ⊢
    linarith [h1]
  have hx0 : (0:ℝ) < (x:ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_one hx1
  have hr_nonneg : (0:ℝ) ≤ (((P α Q * x) % Q : ℕ):ℝ) := Nat.cast_nonneg _
  -- (i) m/x ≤ P/Q
  have hi : (((P α Q * x) / Q : ℕ):ℝ) / (x:ℝ) ≤ (P α Q : ℝ) / (Q:ℝ) := by
    rw [div_le_div_iff₀ hx0 (hQ0 hα hα0 hQ)]
    nlinarith [hdmR, hr_nonneg]
  -- (ii) x*α < m
  have hii : (x:ℝ) * α < (((P α Q * x) / Q : ℕ):ℝ) := by
    have heps : eps α Q = (P α Q : ℝ) - (Q:ℝ) * α := by simp only [eps]
    rw [heps] at hlt
    have key : (Q:ℝ) * ((x:ℝ) * α) < (Q:ℝ) * (((P α Q * x) / Q : ℕ):ℝ) := by
      nlinarith [hlt, hdmR]
    exact lt_of_mul_lt_mul_left key (le_of_lt (hQ0 hα hα0 hQ))
  -- (iii) ⌈xα⌉ ≤ m, so e(x) ≤ e(Q) — contradicting the strict record
  have hiii : (⌈(x:ℝ) * α⌉ : ℝ) ≤ (((P α Q * x) / Q : ℕ):ℝ) := by
    have h2 : (⌈(x:ℝ) * α⌉ : ℤ) ≤ ((P α Q * x) / Q : ℤ) := Int.ceil_le.mpr hii.le
    calc (⌈(x:ℝ) * α⌉ : ℝ) = (((⌈(x:ℝ) * α⌉ : ℤ)):ℝ) := rfl
      _ ≤ ((((P α Q * x) / Q : ℕ):ℤ):ℝ) := by exact_mod_cast h2
      _ = (((P α Q * x) / Q : ℕ):ℝ) := by norm_cast
  have hiv : approxErr α x ≤ approxErr α Q := by
    have h1 : (⌈(x:ℝ) * α⌉ : ℝ) / (x:ℝ)
        ≤ (((P α Q * x) / Q : ℕ):ℝ) / (x:ℝ) :=
      (div_le_div_iff_of_pos_right hx0).mpr hiii
    have hAQ := approxErr_Q hα hα0 hQ
    rw [hAQ]
    simp only [approxErr]
    linarith [h1, hi]
  have hlt2 := hrec x hx1 hxQ
  linarith

/-! ## The fractional-part formula -/

/-- `{xα} = ((P α Q*x) % Q - x*ε)/Q` for `x < Q` (no wraps by Lemma B). -/
theorem yfrac_formula (hα : Irrational α) (hα0 : 0 < α) (hQ : 1 ≤ Q) (hrec : IsStrictRecord α Q) (x : ℕ) (hx : x < Q) :
    yfrac α x
      = ((((P α Q * x) % Q : ℕ):ℝ) - (x:ℝ) * eps α Q) / (Q:ℝ) := by
  rcases Nat.eq_zero_or_pos x with rfl | hxpos
  · have hy0 : yfrac α 0 = 0 := by
      show Int.fract (((0:ℕ):ℝ) * α) = 0
      simp
    rw [hy0]
    simp
  · have hnowrap : (((P α Q * x) % Q : ℕ):ℝ) ≥ (x:ℝ) * eps α Q :=
      lemmaB_nowrap hα hα0 hQ hrec x (by omega) hx
    have hdm : Q * ((P α Q * x) / Q) + (P α Q * x) % Q
        = P α Q * x := Nat.div_add_mod _ _
    have hdmR : (Q:ℝ) * (((P α Q * x) / Q : ℕ):ℝ) + (((P α Q * x) % Q : ℕ):ℝ)
        = (P α Q : ℝ) * (x:ℝ) := by
      have h1 : ((Q * ((P α Q * x) / Q) + (P α Q * x) % Q : ℕ):ℝ)
          = ((P α Q * x : ℕ):ℝ) := by exact_mod_cast hdm
      push_cast at h1 ⊢
      linarith [h1]
    have hrQ : (((P α Q * x) % Q : ℕ):ℝ) < (Q:ℝ) := by
      have h : (P α Q * x) % Q < Q := Nat.mod_lt _ (by omega)
      exact_mod_cast h
    have heps_nn : 0 ≤ (x:ℝ) * eps α Q :=
      mul_nonneg (Nat.cast_nonneg _) (le_of_lt (eps_pos hα hα0 hQ))
    set u : ℝ := ((((P α Q * x) % Q : ℕ):ℝ) - (x:ℝ) * eps α Q) / (Q:ℝ)
      with hu
    have hu0 : 0 ≤ u := by
      rw [hu]
      apply div_nonneg _ (le_of_lt (hQ0 hα hα0 hQ))
      linarith [hnowrap]
    have hu1 : u < 1 := by
      rw [hu, div_lt_one (hQ0 hα hα0 hQ)]
      linarith [hrQ, heps_nn]
    have hdecomp : (x:ℝ) * α
        = (((P α Q * x) / Q : ℕ):ℝ) + u := by
      have heps : eps α Q = (P α Q : ℝ) - (Q:ℝ) * α := by
        simp only [eps]
      rw [hu, heps]
      have hQ0' := hQ0 hα hα0 hQ
      field_simp
      nlinarith [hdmR]
    have hfloor : ⌊(x:ℝ) * α⌋ = (((P α Q * x) / Q : ℕ):ℤ) := by
      rw [Int.floor_eq_iff]
      simp only [Int.cast_natCast]
      constructor
      · linarith [hdecomp, hu0]
      · linarith [hdecomp, hu1]
    have hfrac : yfrac α x = u := by
      have h1 : yfrac α x = (x:ℝ) * α - ⌊(x:ℝ) * α⌋ := by
        simp only [yfrac, Int.fract]
      have h2 : ((((P α Q * x) / Q : ℕ):ℤ):ℝ) = ((((P α Q * x) / Q : ℕ)):ℝ) := by
        norm_cast
      rw [h1, hfloor, h2, hdecomp]
      ring
    rw [hfrac]
/-! ## Permutation counting and the discrepancy bound -/

/-- `x ↦ (P α Q*x) % Q` is injective on `range Q` (`P α Q` is a unit mod `Q`). -/
private theorem inj_on_range (hα : Irrational α) (hα0 : 0 < α) (hQ : 1 ≤ Q) (hrec : IsStrictRecord α Q) {x z : ℕ} (hx : x < Q) (hz : z < Q)
    (h : (P α Q * x) % Q = (P α Q * z) % Q) : x = z := by
  haveI : NeZero Q := ⟨by omega⟩
  have hcop := lemmaA_coprime hα hα0 hQ hrec
  have hmod : P α Q * x ≡ P α Q * z [MOD Q] := h
  have hcast : (P α Q : ZMod Q) * (x : ZMod Q)
      = (P α Q : ZMod Q) * (z : ZMod Q) := by
    have h1 : ((P α Q * x : ℕ) : ZMod Q) = ((P α Q * z : ℕ) : ZMod Q) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    simpa [Nat.cast_mul] using h1
  let u := ZMod.unitOfCoprime (P α Q) hcop
  have hu : (u : ZMod Q) = (P α Q : ZMod Q) := ZMod.coe_unitOfCoprime _ hcop
  have h2 : (u : ZMod Q) * (x : ZMod Q) = (u : ZMod Q) * (z : ZMod Q) := by
    rw [hu]; exact hcast
  have hinj := IsUnit.mul_right_injective (⟨u, rfl⟩ : IsUnit (u : ZMod Q))
  have hxz : (x : ZMod Q) = (z : ZMod Q) := hinj h2
  have hmod2 : x ≡ z [MOD Q] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hxz
  exact hmod2.eq_of_lt_of_lt hx hz

/-- The residues `(P α Q*x) % Q` permute `range Q`. -/
private theorem perm_image (hα : Irrational α) (hα0 : 0 < α) (hQ : 1 ≤ Q) (hrec : IsStrictRecord α Q) :
    (Finset.range Q).image (fun x => (P α Q * x) % Q) = Finset.range Q := by
  apply Finset.eq_of_subset_of_card_le
  · intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    rw [Finset.mem_range] at hx ⊢
    exact Nat.mod_lt _ (by omega)
  · have hinj : Set.InjOn (fun x => (P α Q * x) % Q) ↑(Finset.range Q) := by
      intro x hx z hz h
      rw [Finset.mem_coe, Finset.mem_range] at hx hz
      exact inj_on_range hα hα0 hQ hrec hx hz h
    have hci := Finset.card_image_of_injOn hinj
    rw [hci]

/-- Coupling: `#{x < Q : y_x ≤ j/Q} ≥ j+1` for `j < Q`. -/
theorem count_le (hα : Irrational α) (hα0 : 0 < α) (hQ : 1 ≤ Q) (hrec : IsStrictRecord α Q) (j : ℕ) (hj : j < Q) :
    j + 1 ≤ ((Finset.range Q).filter (fun x => yfrac α x ≤ (j:ℝ)/(Q:ℝ))).card := by
  have hsub : (Finset.range Q).filter (fun x => (P α Q * x) % Q ≤ j) ⊆
      (Finset.range Q).filter (fun x => yfrac α x ≤ (j:ℝ)/(Q:ℝ)) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    obtain ⟨hxQ, hle⟩ := hx
    refine ⟨hxQ, ?_⟩
    rw [yfrac_formula hα hα0 hQ hrec x (Finset.mem_range.mp hxQ),
      div_le_div_iff_of_pos_right (hQ0 hα hα0 hQ)]
    have h1 : (((P α Q * x) % Q : ℕ):ℝ) ≤ (j:ℝ) := by exact_mod_cast hle
    have h2 : 0 ≤ (x:ℝ) * eps α Q :=
      mul_nonneg (Nat.cast_nonneg _) (le_of_lt (eps_pos hα hα0 hQ))
    linarith
  have hcard : ((Finset.range Q).filter (fun x => (P α Q * x) % Q ≤ j)).card
      = j + 1 := by
    have hbij : ((Finset.range Q).filter (fun x => (P α Q * x) % Q ≤ j)).image
        (fun x => (P α Q * x) % Q)
        = (Finset.range Q).filter (fun r => r ≤ j) := by
      ext r
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨x, ⟨hxQ, hle⟩, rfl⟩
        exact ⟨Nat.mod_lt _ (by omega), hle⟩
      · rintro ⟨hrQ, hrj⟩
        have hmem : r ∈ (Finset.range Q).image (fun x => (P α Q * x) % Q) := by
          rw [perm_image hα hα0 hQ hrec]
          exact Finset.mem_range.mpr hrQ
        rw [Finset.mem_image] at hmem
        obtain ⟨x, hxQ, rfl⟩ := hmem
        exact ⟨x, ⟨Finset.mem_range.mp hxQ, hrj⟩, rfl⟩
    have hcard2 : ((Finset.range Q).filter (fun x => (P α Q * x) % Q ≤ j)).card
        = ((Finset.range Q).filter (fun r => r ≤ j)).card := by
      have hinj : Set.InjOn (fun x => (P α Q * x) % Q)
          ↑((Finset.range Q).filter (fun x => (P α Q * x) % Q ≤ j)) := by
        intro x hx z hz h
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hz
        exact inj_on_range hα hα0 hQ hrec hx.1 hz.1 h
      have hci := Finset.card_image_of_injOn hinj
      rw [hbij] at hci
      exact hci.symm
    rw [hcard2]
    have hfin : (Finset.range Q).filter (fun r => r ≤ j) = Finset.range (j+1) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hfin, Finset.card_range]
  rw [← hcard]
  exact Finset.card_le_card hsub

/-! ## C29 main theorem -/

/-- C29 (R52): `D_Q(t) ≥ 0` on `[0,1]` — in fact `> 0` on `(0,1)`. -/
theorem c29 (hα : Irrational α) (hα0 : 0 < α) (hQ : 1 ≤ Q) (hrec : IsStrictRecord α Q) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (Q : ℝ) * t ≤ (((Finset.range Q).filter (fun x => yfrac α x < t)).card : ℝ) := by
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · rw [mul_zero]
    exact Nat.cast_nonneg _
  · have htQ0 : 0 ≤ t * Q := mul_nonneg htpos.le (le_of_lt (hQ0 hα hα0 hQ))
    set j := ⌊t * Q⌋₊ with hjdef
    have hjt : (j:ℝ) ≤ t * Q := by
      rw [hjdef]; exact Nat.floor_le htQ0
    have hjQ : j ≤ Q := by
      have h1 : t * Q ≤ (Q:ℝ) := by
        have hle : t * Q ≤ 1 * Q := by nlinarith [ht1, le_of_lt (hQ0 hα hα0 hQ)]
        simpa using hle
      have h2 : (j:ℝ) ≤ (Q:ℝ) := le_trans hjt h1
      exact_mod_cast h2
    rcases eq_or_lt_of_le hjQ with hjQeq | hjQlt
    · -- `j = Q` forces `t = 1`
      have ht1' : t = 1 := by
        have h1 : (Q:ℝ) ≤ t * Q := by
          have hjt' : (j:ℝ) ≤ t * (Q:ℝ) := hjt
          have hje : (j:ℝ) = (Q:ℝ) := by exact_mod_cast hjQeq
          rw [hje] at hjt'
          exact hjt'
        have h2 : (1:ℝ) ≤ t := by
          by_contra hcon
          push Not at hcon
          have hlt : t * Q < 1 * Q := by nlinarith [hcon, hQ0 hα hα0 hQ]
          linarith [h1, hlt]
        linarith [ht1]
      subst ht1'
      have hcard : (Finset.range Q).filter (fun x => yfrac α x < 1)
          = Finset.range Q := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · intro h; exact h.1
        · intro hx; exact ⟨hx, Int.fract_lt_one _⟩
      rw [hcard, Finset.card_range]
      simp
    · -- `j < Q`: the coupling gives `Q*t < j+1 ≤ #{y_x < t}`
      have hjt' : (j:ℝ)/(Q:ℝ) ≤ t := by
        rw [div_le_iff₀ (hQ0 hα hα0 hQ)]
        have hjt2 : (j:ℝ) ≤ t * Q := hjt
        linarith [hjt2]
      have hsub : (Finset.range Q).filter (fun x => yfrac α x ≤ (j:ℝ)/(Q:ℝ)) ⊆
          (Finset.range Q).filter (fun x => yfrac α x < t) := by
        intro x hx
        rw [Finset.mem_filter] at hx ⊢
        obtain ⟨hxQ, hle⟩ := hx
        refine ⟨hxQ, ?_⟩
        rcases eq_or_lt_of_le hle with heq | hlt
        · rcases Nat.eq_zero_or_pos x with rfl | hxpos
          · have hy0 : yfrac α 0 = 0 := by
              show Int.fract (((0:ℕ):ℝ) * α) = 0
              simp
            rw [hy0]; exact htpos
          · exfalso
            -- `x*ε = r_x - j ∈ ℤ`, contradicting irrationality of `α`
            have h1 := yfrac_formula hα hα0 hQ hrec x (Finset.mem_range.mp hxQ)
            rw [heq] at h1
            have hQ0'' : (Q:ℝ) ≠ 0 := ne_of_gt (hQ0 hα hα0 hQ)
            rw [div_eq_div_iff hQ0'' hQ0''] at h1
            have h2 : (j:ℝ)
                = (((P α Q * x) % Q : ℕ):ℝ) - (x:ℝ) * eps α Q :=
              mul_right_cancel₀ hQ0'' h1
            have hmem : (x:ℝ) * eps α Q
                = (((P α Q * x) % Q : ℕ):ℝ) - (j:ℝ) := by linarith [h2]
            have hxeps : ¬ ∃ k : ℤ, (x:ℝ) * eps α Q = (k:ℝ) := by
              rintro ⟨k, hk⟩
              have heps : eps α Q
                  = (P α Q : ℝ) - (Q:ℝ) * α := by simp only [eps]
              rw [heps] at hk
              have h3 : (x:ℝ) * ((Q:ℝ) * α)
                  = (x:ℝ) * (P α Q : ℝ) - (k:ℝ) := by linarith [hk]
              have h4 : ((x * Q : ℕ):ℝ) * α = (x:ℝ) * ((Q:ℝ) * α) := by
                push_cast; ring
              have h5 : ((x * P α Q : ℕ):ℝ)
                  = (x:ℝ) * (P α Q : ℝ) := by push_cast; ring
              have h2' : ((x * Q : ℕ):ℝ) * α
                  = ((x * P α Q : ℕ):ℝ) - (k:ℝ) := by
                rw [h4, h5]; exact h3
              have hQQ : (0:ℝ) < ((x * Q : ℕ):ℝ) := by
                have hpos : 0 < x * Q := Nat.mul_pos (by omega) (by omega)
                exact_mod_cast hpos
              refine hα ⟨((x * P α Q : ℤ) - k : ℚ) / ((x * Q : ℕ) : ℚ), ?_⟩
              have hQQ0 : ((x:ℝ) * (Q:ℝ)) ≠ 0 := by
                have hpos : 0 < x * Q := Nat.mul_pos (by omega) (by omega)
                have h1 : (0:ℝ) < ((x * Q : ℕ):ℝ) := by exact_mod_cast hpos
                have h2 : (((x * Q : ℕ)):ℝ) = (x:ℝ) * (Q:ℝ) := by push_cast; ring
                rw [h2] at h1
                exact ne_of_gt h1
              push_cast
              rw [div_eq_iff hQQ0]
              push_cast
              push_cast at h2'
              linarith [h2']
            exact hxeps ⟨(((P α Q * x) % Q : ℕ):ℤ) - (j:ℤ), by
              rw [hmem]
              simp only [Int.cast_sub, Int.cast_natCast]⟩
        · exact lt_of_lt_of_le hlt hjt'
      have hstep1 : (Q:ℝ) * t < ((j+1 : ℕ):ℝ) := by
        have hlt1 : t * Q < (j:ℝ) + 1 := by
          rw [hjdef]
          exact Nat.lt_floor_add_one (t * Q)
        push_cast
        linarith [hlt1]
      have hstep2 : ((j+1 : ℕ):ℝ)
          ≤ ((((Finset.range Q).filter (fun x => yfrac α x ≤ (j:ℝ)/(Q:ℝ))).card : ℕ):ℝ) :=
        Nat.cast_le.mpr (count_le hα hα0 hQ hrec j hjQlt)
      have hstep3 : ((((Finset.range Q).filter (fun x => yfrac α x ≤ (j:ℝ)/(Q:ℝ))).card : ℕ):ℝ)
          ≤ ((((Finset.range Q).filter (fun x => yfrac α x < t)).card : ℕ):ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hsub)
      have hlt : (Q:ℝ) * t < ((((Finset.range Q).filter (fun x => yfrac α x < t)).card : ℕ):ℝ) :=
        lt_of_lt_of_le (lt_of_lt_of_le hstep1 hstep2) hstep3
      exact le_of_lt hlt

end CollatzGapC29
