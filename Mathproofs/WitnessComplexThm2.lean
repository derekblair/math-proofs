import Mathlib

/-!
# Witness-complex theorems (Rounds 126, 131, 137)

Formalizes two results from the divisor-conditioned witness complex W(M)
(R126, `~/workspace/math-unsolved/ROUND126_DOSSIER.md`):

1. **R131's b(0)-vacuity lemma** (`b0_vacuity`): for every Type-I Erdős–Straus
   family (a, d, f) with w = 4ad and e = (4a²d+1)/f, at every positive lift
   s ≥ 1 with s ≡ −f (mod w), the parameter b(0) = m₀·e − a (m₀ = (s+f)/w)
   satisfies b(0) ≥ 1. Pure ℕ divisibility; the proof is the dossier's:
   m₀·w = s+f ≥ f+1, so m₀·e·w ≥ (f+1)·e = (4a²d+1)+e ≥ 4a²d+2 > 4a²d = a·w,
   forcing m₀·e > a, and b(0) ≥ 1 since b(0) is a natural number.
   This sharpens R126's Thm 1(b): its "valid iff b(0) ≥ 1" never binds.

2. **R126's Thm 2 (fiber collision law)** (`fiber_collision_law`): for q ≥ 1
   and units u, u′ in `ZMod q` (the paper's c, c′ — units since gcd(c,q) = 1),
   γ_q(a,c,d) = γ_q(a′,c′,d′) ⟺ a·u′ = a′·u,
   where γ_q(a,c,d) = −a·u⁻¹. Forward: cancel the negations, multiply by u·u′.
   Backward: multiply the hypothesis by u⁻¹·u′⁻¹. Stated with explicit units
   to avoid `ZMod`'s gcdA-based `Inv` instance (R133's flagged fiddliness);
   the unit equations are `Units.inv_mul` directly.
-/

namespace WitnessComplexThm2

/-- R131's b(0)-vacuity lemma (Round 131, [PROVED*] → machine-checked here).

For a Type-I family (a, d, f) with e·f = 4a²d+1, at every positive lift
s ≥ 1 with 4ad ∣ (s+f) (so m₀ = (s+f)/(4ad) is the lift multiplier),
b(0) = m₀·e − a ≥ 1. -/
theorem b0_vacuity {a d f s m₀ e : ℕ}
    (_ha : 1 ≤ a) (_hd : 1 ≤ d) (_hf : 1 ≤ f)
    (he : e * f = 4 * a ^ 2 * d + 1)
    (hs : 1 ≤ s)
    (_hlift : 4 * a * d ∣ s + f)
    (hm0 : m₀ * (4 * a * d) = s + f) :
    1 ≤ m₀ * e - a := by
  -- e ≥ 1: e = 0 would make e·f = 0, contradicting he (RHS ≥ 1).
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | hpos
    · rw [zero_mul] at he
      exact absurd he.symm (Nat.succ_ne_zero _)
    · exact hpos
  -- m₀·w = s + f ≥ f + 1 since s ≥ 1.
  have hmw : f + 1 ≤ m₀ * (4 * a * d) := by rw [hm0]; omega
  -- The core: m₀·e > a. By contradiction: m₀·e ≤ a gives
  -- 4a²d + 2 ≤ m₀·e·w ≤ a·w = 4a²d, impossible.
  have hme : a < m₀ * e := by
    by_contra h
    push Not at h
    have h2 : (f + 1) * e ≤ (m₀ * (4 * a * d)) * e :=
      mul_le_mul_of_nonneg_right hmw (Nat.zero_le _)
    have h3 : (m₀ * e) * (4 * a * d) ≤ a * (4 * a * d) :=
      mul_le_mul_of_nonneg_right h (Nat.zero_le _)
    have h5 : a * (4 * a * d) = 4 * a ^ 2 * d := by ring
    have h4 : a * (4 * a * d) + 2 ≤ m₀ * e * (4 * a * d) := by
      have h4a : 4 * a ^ 2 * d + 2 ≤ e * f + e := by
        rw [he]
        exact Nat.add_le_add_left he1 _
      calc a * (4 * a * d) + 2 = 4 * a ^ 2 * d + 2 := by rw [h5]
        _ ≤ e * f + e := h4a
        _ = (f + 1) * e := by ring
        _ ≤ (m₀ * (4 * a * d)) * e := h2
        _ = m₀ * e * (4 * a * d) := by ring
    have h6 : 4 * a ^ 2 * d + 2 ≤ 4 * a ^ 2 * d := by
      rw [← h5]; exact Nat.le_trans h4 h3
    have hlt : 4 * a ^ 2 * d < 4 * a ^ 2 * d + 2 :=
      calc 4 * a ^ 2 * d < 4 * a ^ 2 * d + 1 := Nat.lt_succ_self _
        _ < 4 * a ^ 2 * d + 2 := Nat.lt_succ_self _
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt h6)
  omega

/-- R126's Thm 2: the fiber class-map collision law.

In `ZMod q`, for units u, u′ (the paper's c, c′ — units since gcd(c,q) = 1),
−a·u⁻¹ = −a′·u′⁻¹ ⟺ a·u′ = a′·u.
Forward: cancel the negations, then multiply by u·u′.
Backward: multiply the hypothesis by u⁻¹·u′⁻¹. -/
theorem fiber_collision_law {q : ℕ}
    {a a' : ZMod q} (u u' : (ZMod q)ˣ) :
    (-a * ((u⁻¹ : (ZMod q)ˣ) : ZMod q) = -a' * ((u'⁻¹ : (ZMod q)ˣ) : ZMod q)) ↔
      (a * (u' : ZMod q) = a' * (u : ZMod q)) := by
  have hcc : ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * (u : ZMod q) = 1 := Units.inv_mul u
  have hcc' : ((u'⁻¹ : (ZMod q)ˣ) : ZMod q) * (u' : ZMod q) = 1 := Units.inv_mul u'
  constructor
  · intro h
    have h2 : a * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)
        = a' * ((u'⁻¹ : (ZMod q)ˣ) : ZMod q) := by
      have h' := congrArg (fun x : ZMod q => -x) h
      simpa [neg_mul] using h'
    have hL : (a * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) * ((u : ZMod q) * (u' : ZMod q))
        = a * (u' : ZMod q) := by
      calc (a * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) * ((u : ZMod q) * (u' : ZMod q))
          = (a * (u' : ZMod q))
            * (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * (u : ZMod q)) := by ring
        _ = (a * (u' : ZMod q)) * 1 := by rw [hcc]
        _ = a * (u' : ZMod q) := by ring
    have hR : (a' * ((u'⁻¹ : (ZMod q)ˣ) : ZMod q)) * ((u : ZMod q) * (u' : ZMod q))
        = a' * (u : ZMod q) := by
      calc (a' * ((u'⁻¹ : (ZMod q)ˣ) : ZMod q)) * ((u : ZMod q) * (u' : ZMod q))
          = (a' * (u : ZMod q))
            * (((u'⁻¹ : (ZMod q)ˣ) : ZMod q) * (u' : ZMod q)) := by ring
        _ = (a' * (u : ZMod q)) * 1 := by rw [hcc']
        _ = a' * (u : ZMod q) := by ring
    have key : (a * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) * ((u : ZMod q) * (u' : ZMod q))
        = (a' * ((u'⁻¹ : (ZMod q)ˣ) : ZMod q)) * ((u : ZMod q) * (u' : ZMod q)) := by
      rw [h2]
    rw [hL, hR] at key
    exact key
  · intro h
    have h2 : a * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)
        = a' * ((u'⁻¹ : (ZMod q)ˣ) : ZMod q) := by
      calc a * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)
          = (a * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) * 1 := by ring
        _ = (a * ((u⁻¹ : (ZMod q)ˣ) : ZMod q))
              * (((u'⁻¹ : (ZMod q)ˣ) : ZMod q) * (u' : ZMod q)) := by rw [hcc']
        _ = (a * (u' : ZMod q))
              * (((u⁻¹ : (ZMod q)ˣ) : ZMod q)
                * ((u'⁻¹ : (ZMod q)ˣ) : ZMod q)) := by ring
        _ = (a' * (u : ZMod q))
              * (((u⁻¹ : (ZMod q)ˣ) : ZMod q)
                * ((u'⁻¹ : (ZMod q)ˣ) : ZMod q)) := by rw [h]
        _ = (a' * ((u'⁻¹ : (ZMod q)ˣ) : ZMod q))
              * (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * (u : ZMod q)) := by ring
        _ = (a' * ((u'⁻¹ : (ZMod q)ˣ) : ZMod q)) * 1 := by rw [hcc]
        _ = a' * ((u'⁻¹ : (ZMod q)ˣ) : ZMod q) := by ring
    have h' := congrArg (fun x : ZMod q => -x) h2
    simpa [neg_mul] using h'

end WitnessComplexThm2
