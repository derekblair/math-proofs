/-
  ESBranchTwo.lean — R209 branch-2 degeneracy + divisor-closed family theorem (with the mod-8 refutation of the naive form).

  Paper: papers/fiber-compatibility-composite-suppression-October-11-2026/
  Status: [PROVED] — branch2_collapse, branch2_m_le_s, family_identity, branch2_m_mod8_refuted
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); machine-checked on bakkie (R218), `lake build` exit 0, zero sorrys, axioms standard-only.
-/

import Mathlib.Tactic
import Mathlib.Algebra.Field.Basic

/-!
Round 218 (lane 4) — Lean formalization of R209's branch-2 degeneracy theorem
(parts (1), (2), (3) and the divisibility shape (5)) and the divisor-closed family
theorem (the 92-identity parametric family), plus the s = 49 witness.

Source: ~/workspace/math-unsolved/ROUND209_DOSSIER.md

IMPORTANT (found during formalization): R209's claim (4),
"m ≤ 2·gcd(XSTEP,(s+m)/4), hence m ≡ 7 (mod 8)", is FALSE as stated.
Its proof argues "m ≥ 3 forces g ≥ 2, so 2 ∣ x₀" — but g ≥ 2 does not imply
2 ∣ g. The theorem `branch2_m_mod8_refuted` below exhibits a genuine branch-2
identity (XSTEP = 15, s = 97, m = 3, A = 10, r₁ = 2, p = 3, q = 5, x₀ = 25)
satisfying every hypothesis of (4), with the identity verified for all t,
yet m = 3 ≢ 7 (mod 8). So (4) is NOT formalized; it is refuted, and the
[PR0VED*] label on R209 (4) must be withdrawn.

Checked with Lean 4.34.1 (leanprover/lean4:stable) + Mathlib.
-/

namespace ESBranchTwo

/-- R209 (1): w = r·s/M ∈ ℤ (i.e. M ∣ r·s) and gcd(s,M) = 1 force M ∣ r.
Consequence: any branch-2 search with r < M is provably vacuous. -/
theorem branch2_M_dvd_r (M s r : ℕ) (_hM : 0 < M) (hdvd : M ∣ r * s)
    (hcop : Nat.Coprime s M) : M ∣ r := by
  rw [mul_comm] at hdvd
  exact (hcop.symm).dvd_of_dvd_mul_left hdvd

/-- R209 (2), setup: with x = XSTEP·t + x₀, n = M·t + s, M = 4·XSTEP and
4·x₀ = s + m, the "cubic" relation collapses to the linear 4x = n + m. -/
theorem branch2_four_x_eq (XSTEP t x₀ M s m : ℤ) (hM : M = 4 * XSTEP)
    (hx : 4 * x₀ = s + m) : 4 * (XSTEP * t + x₀) = (M * t + s) + m := by
  linear_combination (-t) * hM + hx

/-- R209 (2), core: the only nontrivial content of branch 2 is the coefficient
identity (r₁+A)·x = m·A·r₁·C, i.e. C/x = (r₁+A)/(m·A·r₁) is constant.
From the coefficient equations it follows for the linear forms. -/
theorem branch2_collapse (A r₁ XSTEP x₀ p q m t : ℤ)
    (h1 : (r₁ + A) * XSTEP = m * A * r₁ * p)
    (h2 : (r₁ + A) * x₀ = m * A * r₁ * q) :
    (r₁ + A) * (XSTEP * t + x₀) = m * A * r₁ * (p * t + q) := by
  linear_combination t * h1 + h2

/-- R209 (3): m ≤ s. From q = p(s+m)/M ≥ 1 (i.e. p(s+m) = M·q) and
p ≤ 2·XSTEP/m (i.e. p·m ≤ 2·XSTEP), with M = 4·XSTEP. -/
theorem branch2_m_le_s (p m s XSTEP q : ℕ) (hp : 0 < p) (_hm : 0 < m)
    (hq : 1 ≤ q) (_hX : 0 < XSTEP) (hpm : p * m ≤ 2 * XSTEP)
    (hQ : p * (s + m) = 4 * XSTEP * q) : m ≤ s := by
  by_contra hlt
  push Not at hlt
  have hps : p * s < p * m := Nat.mul_lt_mul_of_pos_left hlt hp
  have e1 : p * (s + m) = p * s + p * m := by ring
  have e4 : 4 * XSTEP ≤ p * (s + m) := by
    calc 4 * XSTEP = 4 * XSTEP * 1 := by ring
    _ ≤ 4 * XSTEP * q := Nat.mul_le_mul_left _ hq
    _ = p * (s + m) := hQ.symm
  omega

/-- R209 (5), first step: from (r₁+A)·XSTEP = m·A·r₁·p we get
A·r₁ ∣ (r₁+A)·XSTEP. -/
theorem branch2_divisibility_shape (A r₁ XSTEP m p : ℕ)
    (h : (r₁ + A) * XSTEP = m * A * r₁ * p) :
    A * r₁ ∣ (r₁ + A) * XSTEP :=
  ⟨m * p, by rw [h]; ring⟩

-- Auxiliary: a ∣ a + b and b ∣ a + b are each coprime to a + b, given a ⊥ b.
private theorem coprime_add_left_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    Nat.Coprime a (a + b) := by
  apply Nat.coprime_of_dvd
  intro k hkprime hka hkab
  have hkb : k ∣ b := by
    have hsub : k ∣ (a + b) - a := Nat.dvd_sub hkab hka
    rwa [Nat.add_sub_cancel_left] at hsub
  have hckb : Nat.Coprime k b := h.coprime_dvd_left hka
  exact (Nat.Prime.coprime_iff_not_dvd hkprime).mp hckb hkb

/-- R209 (5), full: writing A = g₁·a, r₁ = g₁·b with gcd(a,b) = 1,
the divisibility A·r₁ ∣ (r₁+A)·XSTEP forces a·b ∣ XSTEP
(since gcd(a·b, a+b) = 1). -/
theorem branch2_ab_dvd_XSTEP (g₁ a b XSTEP : ℕ) (hg : 0 < g₁)
    (hcop : Nat.Coprime a b)
    (hdvd : (g₁ * a) * (g₁ * b) ∣ ((g₁ * b) + (g₁ * a)) * XSTEP) :
    a * b ∣ XSTEP := by
  have e1 : (g₁ * a) * (g₁ * b) = g₁ * (g₁ * (a * b)) := by ring
  have e2 : ((g₁ * b) + (g₁ * a)) * XSTEP = g₁ * ((a + b) * XSTEP) := by ring
  rw [e1, e2] at hdvd
  have hcancel : g₁ * (a * b) ∣ (a + b) * XSTEP :=
    (Nat.mul_dvd_mul_iff_left hg).mp hdvd
  obtain ⟨k, hk⟩ := hcancel
  have hab : a * b ∣ (a + b) * XSTEP := ⟨g₁ * k, by rw [hk]; ring⟩
  have hca : Nat.Coprime a (a + b) := coprime_add_left_of_coprime hcop
  have hcb : Nat.Coprime b (a + b) := by
    rw [add_comm a b]
    exact coprime_add_left_of_coprime (hcop.symm)
  have hcop2 : Nat.Coprime (a * b) (a + b) := by
    rw [Nat.coprime_mul_iff_left]
    exact ⟨hca, hcb⟩
  exact hcop2.dvd_of_dvd_mul_left hab

/-- R209 family theorem, integrality: for s = 264k + 73 the denominators
(s+15)/4, (s+15)/44, (3s+1)/4 are integers. -/
theorem family_integrality (k : ℕ) :
    44 ∣ 264 * k + 73 + 15 ∧ 4 ∣ 264 * k + 73 + 15 ∧
      4 ∣ 3 * (264 * k + 73) + 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- R209 family theorem: the 92 reachable targets are exactly s ≡ 73 (mod 264),
all sharing (c,m,A,r) = (4,15,1,46410). For every k, with s = 264k+73,
4/n = 1/x + 1/(n·C) + 1/(B·C) where n = 2042040t+s, x = 510510t+(s+15)/4,
B = 46410t+(s+15)/44, C = 1531530t+(3s+1)/4. -/
theorem family_identity (t k : ℕ) :
    (4 : ℚ) / ((2042040 : ℚ) * t + (264 * (k : ℚ) + 73))
      = 1 / ((510510 : ℚ) * t + (264 * (k : ℚ) + 73 + 15) / 4)
      + 1 / (((2042040 : ℚ) * t + (264 * (k : ℚ) + 73))
          * ((1531530 : ℚ) * t + (3 * (264 * (k : ℚ) + 73) + 1) / 4))
      + 1 / (((46410 : ℚ) * t + (264 * (k : ℚ) + 73 + 15) / 44)
          * ((1531530 : ℚ) * t + (3 * (264 * (k : ℚ) + 73) + 1) / 4)) := by
  have hn : (0 : ℚ) < (2042040 : ℚ) * t + (264 * (k : ℚ) + 73) := by positivity
  have hx : (0 : ℚ) < (510510 : ℚ) * t + (264 * (k : ℚ) + 73 + 15) / 4 := by
    positivity
  have hB : (0 : ℚ) < (46410 : ℚ) * t + (264 * (k : ℚ) + 73 + 15) / 44 := by
    positivity
  have hC : (0 : ℚ) < (1531530 : ℚ) * t + (3 * (264 * (k : ℚ) + 73) + 1) / 4 := by
    positivity
  have hn' := ne_of_gt hn
  have hx' := ne_of_gt hx
  have hB' := ne_of_gt hB
  have hC' := ne_of_gt hC
  have hnc : ((2042040 : ℚ) * t + (264 * (k : ℚ) + 73))
      * ((1531530 : ℚ) * t + (3 * (264 * (k : ℚ) + 73) + 1) / 4) ≠ 0 :=
    mul_ne_zero hn' hC'
  have hBc : ((46410 : ℚ) * t + (264 * (k : ℚ) + 73 + 15) / 44)
      * ((1531530 : ℚ) * t + (3 * (264 * (k : ℚ) + 73) + 1) / 4) ≠ 0 :=
    mul_ne_zero hB' hC'
  field_simp
  ring

/-- R209 branch-2 witness: s = 49, m = 7, A = r₁ = 1 gives p = 145860, q = 4,
a genuine (degenerate, repeated-term) branch-2 identity for all t. -/
theorem branch2_witness_s49 (t : ℕ) :
    (4 : ℚ) / ((2042040 : ℚ) * t + 49)
      = 1 / ((510510 : ℚ) * t + 14)
      + 2 / (((2042040 : ℚ) * t + 49) * ((145860 : ℚ) * t + 4)) := by
  have hn : (0 : ℚ) < (2042040 : ℚ) * t + 49 := by positivity
  have hx : (0 : ℚ) < (510510 : ℚ) * t + 14 := by positivity
  have hC : (0 : ℚ) < (145860 : ℚ) * t + 4 := by positivity
  have hn' := ne_of_gt hn
  have hx' := ne_of_gt hx
  have hC' := ne_of_gt hC
  have hnc : ((2042040 : ℚ) * t + 49) * ((145860 : ℚ) * t + 4) ≠ 0 :=
    mul_ne_zero hn' hC'
  field_simp
  ring

/-- The hypotheses of R209 (4) hold at (XSTEP, s, m, p, x₀) = (15, 97, 3, 3, 25):
s ≡ 1 (mod 8), 4 ∣ s+m, x₀·4 = s+m, XSTEP ∣ p·x₀, p·m ≤ 2·XSTEP, m ≥ 3,
m ≡ 3 (mod 4), s ≡ 1 (mod 24). -/
theorem branch2_mod8_counterexample_hyps :
    (97 : ℕ) % 8 = 1 ∧ 4 ∣ 97 + 3 ∧ 25 * 4 = 97 + 3 ∧ 15 ∣ 3 * 25 ∧
      3 * 3 ≤ 2 * 15 ∧ 3 ≤ 3 ∧ (3 : ℕ) % 4 = 3 ∧ (97 : ℕ) % 24 = 1 := by
  decide

/-- ...and it is a genuine branch-2 identity for all t:
XSTEP = 15, M = 60, s = 97, m = 3, A = 10, r₁ = 2 (so r = 120, B = 2n),
C = 3t+5, x = 15t+25. Indeed m·A·r₁·C = 60(3t+5) = (A+r₁)·x = 12(15t+25). -/
theorem branch2_mod8_counterexample_identity (t : ℕ) :
    (4 : ℚ) / ((60 : ℚ) * t + 97)
      = 1 / ((15 : ℚ) * t + 25)
      + 1 / (((60 : ℚ) * t + 97) * 10 * ((3 : ℚ) * t + 5))
      + 1 / ((2 * ((60 : ℚ) * t + 97)) * ((3 : ℚ) * t + 5)) := by
  have hn : (0 : ℚ) < (60 : ℚ) * t + 97 := by positivity
  have hx : (0 : ℚ) < (15 : ℚ) * t + 25 := by positivity
  have hC : (0 : ℚ) < (3 : ℚ) * t + 5 := by positivity
  have hn' := ne_of_gt hn
  have hx' := ne_of_gt hx
  have hC' := ne_of_gt hC
  have hnc : ((60 : ℚ) * t + 97) * ((3 : ℚ) * t + 5) ≠ 0 :=
    mul_ne_zero hn' hC'
  have hnC : ((60 : ℚ) * t + 97) * 10 * ((3 : ℚ) * t + 5) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero hn' (by norm_num)
    · exact hC'
  have hBC : (2 * ((60 : ℚ) * t + 97)) * ((3 : ℚ) * t + 5) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hn') hC'
  field_simp
  ring

/-- ...yet m = 3 ≢ 7 (mod 8). Hence R209 (4), "m ≤ 2·gcd(XSTEP,(s+m)/4),
hence m ≡ 7 (mod 8)", is FALSE as stated: the step "m ≥ 3 forces g ≥ 2,
so 2 ∣ x₀" is invalid (here g = gcd(15,25) = 5 ≥ 2 but 2 ∤ 25). -/
theorem branch2_m_mod8_refuted :
    ((97 : ℕ) % 8 = 1 ∧ 4 ∣ 97 + 3 ∧ 25 * 4 = 97 + 3 ∧ 15 ∣ 3 * 25 ∧
      3 * 3 ≤ 2 * 15 ∧ 3 ≤ 3 ∧ (3 : ℕ) % 4 = 3 ∧ (97 : ℕ) % 24 = 1)
    ∧ (3 : ℕ) % 8 ≠ 7 :=
  ⟨branch2_mod8_counterexample_hyps, by decide⟩

#print axioms branch2_M_dvd_r
#print axioms branch2_four_x_eq
#print axioms branch2_collapse
#print axioms branch2_m_le_s
#print axioms branch2_divisibility_shape
#print axioms branch2_ab_dvd_XSTEP
#print axioms family_integrality
#print axioms family_identity
#print axioms branch2_witness_s49
#print axioms branch2_mod8_counterexample_hyps
#print axioms branch2_mod8_counterexample_identity
#print axioms branch2_m_mod8_refuted

end ESBranchTwo
