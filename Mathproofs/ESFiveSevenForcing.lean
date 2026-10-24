import Mathproofs.ESCovering

/-!
# R140 5/7-forcing lemma (Round 162, Lean formalization lane)

R140 §4 (dossier): the 5/7-forcing lemma.

(a) Every s ∈ S with (s/5) = −1 is T1-covered (via w = 20): s ∈ S forces
    s ≡ 1 (mod 4), and (s/5) = −1 forces s ≡ 2, 3 (mod 5); CRT gives
    s ≡ 13 or 17 (mod 20), both T1 divisor classes (−f mod 20 for
    f | 4·1²·5+1 = 21, f ∈ {1,3,7,21} giving classes {19,17,13}).

(b) Every s ∈ S with (s/7) = −1 is T2-covered (via q = 7): the three
    fibers (a,c,d) ∈ {(1,1,2),(1,2,1),(2,1,1)} (each with acd = 2, so
    4acd−1 = 7) give Γ_7 = {−a·c⁻¹ mod 7} = {6,3,5}, exactly the QNRs
    mod 7.

The arithmetic kernels are followed by constructive covering exports in
`ESCovering.Covered`: positive natural denominators and their rational identity.
The T1 w=20 residue classes are covered by explicit splitting identities.
The T2 q=7 fibers construct their positive quotient and use the checked
`WitnessComplexThm13.t3_full_class` identity. Both full-progression exports
include t=0; they need no cited b(0)-vacuity assertion.

1. `qnr5_char` / `qnr7_char`: QNRs mod 5 are {2,3}; mod 7 are {3,5,6}
   (both by `decide`).
2. `legendre_five_neg_one` / `legendre_seven_neg_one`: Legendre −1 at 5/7
   forces the residue sets (via `quadraticChar_neg_one_iff_not_isSquare`).
3. `t1_five_forcing`: s % 4 = 1 ∧ (s/5) = −1 ⟹ s % 20 ∈ {13, 17} (`omega`).
4. `w20_divisors` / `w20_covered_classes`: the T1 divisor classes at w = 20.
5. `t1_five_forcing_full`: packaged part (a) — the forced class is a T1
   divisor class.
6. `seven_fiber_products`: the three T2 fibers satisfy acd = 2.
7. `gamma7_fiber1` / `gamma7_fiber2` / `gamma7_fiber3`: the three fiber
   values −a·c⁻¹ mod 7 are 6, 3, 5 (inverses discharged by rewrite —
   `decide` cannot kernel-evaluate `⁻¹` in `ZMod 7`).
8. `gamma7_eq_qnr`: Γ_7 equals the QNR set mod 7.
9. `t2_seven_forcing`: packaged part (b) — (s/7) = −1 puts s mod 7 in Γ_7.

The global interpretation of the named sets H and Q remains outside this
module. The local 5/7 coverage claims themselves are proved here.
-/

namespace ESFiveSevenForcing

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- QNRs mod 5 are exactly {2, 3}. -/
theorem qnr5_char : ∀ x : ZMod 5, ¬ IsSquare x → x ≠ 0 →
    x = ((2 : ℕ) : ZMod 5) ∨ x = ((3 : ℕ) : ZMod 5) := by
  decide

/-- QNRs mod 7 are exactly {3, 5, 6}. -/
theorem qnr7_char : ∀ x : ZMod 7, ¬ IsSquare x → x ≠ 0 →
    x = ((3 : ℕ) : ZMod 7) ∨ x = ((5 : ℕ) : ZMod 7) ∨ x = ((6 : ℕ) : ZMod 7) := by
  decide

/-- (s/5) = −1 forces s ≡ 2 or 3 (mod 5). -/
theorem legendre_five_neg_one (s : ℕ) (h : legendreSym 5 (s : ℤ) = -1) :
    s % 5 = 2 ∨ s % 5 = 3 := by
  have hq : quadraticChar (ZMod 5) ((s : ℤ) : ZMod 5) = -1 := h
  rw [quadraticChar_neg_one_iff_not_isSquare] at hq
  push_cast at hq
  have h0 : ((s : ℕ) : ZMod 5) ≠ 0 := by
    intro hcon
    apply hq
    rw [hcon]
    exact ⟨0, by simp⟩
  rcases qnr5_char ((s : ℕ) : ZMod 5) hq h0 with h2 | h3
  · left
    have hmod := (ZMod.natCast_eq_natCast_iff' s 2 5).mp h2
    simpa using hmod
  · right
    have hmod := (ZMod.natCast_eq_natCast_iff' s 3 5).mp h3
    simpa using hmod

/-- (s/7) = −1 forces s ≡ 3, 5 or 6 (mod 7). -/
theorem legendre_seven_neg_one (s : ℕ) (h : legendreSym 7 (s : ℤ) = -1) :
    s % 7 = 3 ∨ s % 7 = 5 ∨ s % 7 = 6 := by
  have hq : quadraticChar (ZMod 7) ((s : ℤ) : ZMod 7) = -1 := h
  rw [quadraticChar_neg_one_iff_not_isSquare] at hq
  push_cast at hq
  have h0 : ((s : ℕ) : ZMod 7) ≠ 0 := by
    intro hcon
    apply hq
    rw [hcon]
    exact ⟨0, by simp⟩
  rcases qnr7_char ((s : ℕ) : ZMod 7) hq h0 with h3 | h5 | h6
  · left
    have hmod := (ZMod.natCast_eq_natCast_iff' s 3 7).mp h3
    simpa using hmod
  · right
    left
    have hmod := (ZMod.natCast_eq_natCast_iff' s 5 7).mp h5
    simpa using hmod
  · right
    right
    have hmod := (ZMod.natCast_eq_natCast_iff' s 6 7).mp h6
    simpa using hmod

/-- Part (a), residue form: s ≡ 1 (mod 4) and (s/5) = −1 force
    s ≡ 13 or 17 (mod 20). -/
theorem t1_five_forcing (s : ℕ) (h4 : s % 4 = 1)
    (hleg : legendreSym 5 (s : ℤ) = -1) :
    s % 20 = 13 ∨ s % 20 = 17 := by
  have h5 := legendre_five_neg_one s hleg
  rcases h5 with h | h <;> omega

/-- The divisors of 21 = 4·1²·5+1. -/
theorem w20_divisors : Nat.divisors 21 = {1, 3, 7, 21} := by
  decide

/-- The T1 divisor classes at w = 20 are {19, 17, 13} = {−f mod 20 : f | 21}. -/
theorem w20_covered_classes (f : ℕ) (hf : f ∣ 21) :
    (20 - f % 20) % 20 = 19 ∨ (20 - f % 20) % 20 = 17 ∨
      (20 - f % 20) % 20 = 13 := by
  have hmem : f ∈ Nat.divisors 21 := Nat.mem_divisors.mpr ⟨hf, by norm_num⟩
  rw [w20_divisors] at hmem
  fin_cases hmem <;> decide

/-- Part (a), residue kernel: the forced class is a T1 divisor class at w = 20.
    `t1_five_covered` below completes the positive-natural covering statement. -/
theorem t1_five_forcing_full (s : ℕ) (h4 : s % 4 = 1)
    (hleg : legendreSym 5 (s : ℤ) = -1) :
    ∃ f : ℕ, f ∣ 21 ∧ s % 20 = (20 - f % 20) % 20 := by
  have hs := t1_five_forcing s h4 hleg
  rcases hs with h | h
  · exact ⟨7, by decide, by omega⟩
  · exact ⟨3, by decide, by omega⟩

/-- The three T2 fibers at q = 7 satisfy acd = 2 (so 4acd − 1 = 7). -/
theorem seven_fiber_products :
    ∀ t ∈ ({(1, 1, 2), (1, 2, 1), (2, 1, 1)} : Finset (ℕ × ℕ × ℕ)),
      t.1 * t.2.1 * t.2.2 = 2 := by
  decide

/-- Fiber (a,c,d) = (1,1,2): γ = −1·1⁻¹ = 6 mod 7.
    (`decide` cannot kernel-evaluate `⁻¹` in `ZMod 7`, so the inverses are
    discharged by rewrite first.) -/
theorem gamma7_fiber1 : (-(1 : ZMod 7)) * (1 : ZMod 7)⁻¹ = 6 := by
  rw [inv_one]; decide

/-- Fiber (a,c,d) = (1,2,1): γ = −1·2⁻¹ = 3 mod 7. -/
theorem gamma7_fiber2 : (-(1 : ZMod 7)) * (2 : ZMod 7)⁻¹ = 3 := by
  have hinv : (2 : ZMod 7)⁻¹ = 4 :=
    (eq_inv_of_mul_eq_one_left (by decide : (4 : ZMod 7) * 2 = 1)).symm
  rw [hinv]; decide

/-- Fiber (a,c,d) = (2,1,1): γ = −2·1⁻¹ = 5 mod 7. -/
theorem gamma7_fiber3 : (-(2 : ZMod 7)) * (1 : ZMod 7)⁻¹ = 5 := by
  rw [inv_one]; decide

/-- Γ_7: the three fiber classes −a·c⁻¹ mod 7 are exactly the QNRs mod 7. -/
theorem gamma7_eq_qnr : ∀ x : ZMod 7,
    (x ≠ 0 ∧ ¬ IsSquare x) ↔
      (x = (-(1 : ZMod 7)) * (1 : ZMod 7)⁻¹ ∨
       x = (-(1 : ZMod 7)) * (2 : ZMod 7)⁻¹ ∨
       x = (-(2 : ZMod 7)) * (1 : ZMod 7)⁻¹) := by
  intro x
  rw [gamma7_fiber1, gamma7_fiber2, gamma7_fiber3]
  constructor
  · rintro ⟨hx0, hxnsq⟩
    have h := qnr7_char x hxnsq hx0
    rcases h with rfl | rfl | rfl <;> decide
  · rintro (rfl | rfl | rfl) <;> decide

/-- Part (b), residue kernel: (s/7) = −1 puts s mod 7 in Γ_7.
    `t2_seven_covered` below constructs the positive-natural witnesses. -/
theorem t2_seven_forcing (s : ℕ) (hleg : legendreSym 7 (s : ℤ) = -1) :
    (s : ZMod 7) = (-(1 : ZMod 7)) * (1 : ZMod 7)⁻¹ ∨
    (s : ZMod 7) = (-(1 : ZMod 7)) * (2 : ZMod 7)⁻¹ ∨
    (s : ZMod 7) = (-(2 : ZMod 7)) * (1 : ZMod 7)⁻¹ := by
  rw [gamma7_fiber1, gamma7_fiber2, gamma7_fiber3]
  have h7 := legendre_seven_neg_one s hleg
  have hmod : (s : ZMod 7) = ((s % 7 : ℕ) : ZMod 7) := by
    rw [ZMod.natCast_eq_natCast_iff']
    simp
  rcases h7 with h | h | h
  · rw [hmod, h]; decide
  · rw [hmod, h]; decide
  · rw [hmod, h]; decide

/-! ## Positive natural covering witnesses -/

/-- The class 13 modulo 20 is covered, including its first member.
The parity split chooses an integral two-fraction split in each case. -/
theorem class13_covered (n : ℕ) (hn : n % 20 = 13) : ESCovering.Covered n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 20*k+13 := ⟨n/20, by omega⟩
  by_cases hk : k % 2 = 0
  · exact ESCovering.of_split (20*k+13) (5*k+4) 3 1 1 2
      (by omega) (by omega) (by decide) (by decide) (by decide)
      (by omega) (by decide) (by omega)
  · exact ESCovering.of_split (20*k+13) (5*k+5) 7 1 2 5
      (by omega) (by omega) (by decide) (by decide) (by decide)
      (by omega) (by decide) (by omega)

/-- The class 17 modulo 20 is covered by the split 3·2 = 1+5. -/
theorem class17_covered (n : ℕ) (hn : n % 20 = 17) : ESCovering.Covered n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 20*k+17 := ⟨n/20, by omega⟩
  exact ESCovering.of_split (20*k+17) (5*k+5) 3 2 1 5
    (by omega) (by omega) (by decide) (by decide) (by decide)
    (by omega) (by decide) (by omega)

/-- The remaining w=20 divisor class is covered by the split 1·2 = 1+1. -/
theorem class19_covered (n : ℕ) (hn : n % 20 = 19) : ESCovering.Covered n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 20*k+19 := ⟨n/20, by omega⟩
  exact ESCovering.of_split (20*k+19) (5*k+5) 1 2 1 1
    (by omega) (by omega) (by decide) (by decide) (by decide)
    (by omega) (by decide) (by omega)

/-- Every T1 divisor class at w=20 yields positive integral Egyptian-fraction
witnesses. The construction uses the explicit residue splits above. -/
theorem t1_w20_class_covered (n f : ℕ) (hf : f ∣ 21)
    (hclass : n % 20 = (20-f%20)%20) : ESCovering.Covered n := by
  rcases w20_covered_classes f hf with h | h | h
  · exact class19_covered n (hclass.trans h)
  · exact class17_covered n (hclass.trans h)
  · exact class13_covered n (hclass.trans h)

/-- The 5-forcing hypotheses produce actual positive natural denominators. -/
theorem t1_five_covered (s : ℕ) (h4 : s % 4 = 1)
    (hleg : legendreSym 5 (s : ℤ) = -1) : ESCovering.Covered s := by
  obtain ⟨f, hf, hclass⟩ := t1_five_forcing_full s h4 hleg
  exact t1_w20_class_covered s f hf hclass

/-- Each of the three q=7 T2 fibers gives positive natural denominators,
using its genuine (a,c,d) parameters and a quotient constructed by divisibility. -/
theorem qnr7_covered (n : ℕ) (hn : n%7 = 3 ∨ n%7 = 5 ∨ n%7 = 6) :
    ESCovering.Covered n := by
  rcases hn with hn | hn | hn
  · exact ESCovering.of_t2 1 2 1 n 7 (by decide) (by decide) (by decide)
      (by omega) (by decide) (by omega)
  · exact ESCovering.of_t2 2 1 1 n 7 (by decide) (by decide) (by decide)
      (by omega) (by decide) (by omega)
  · exact ESCovering.of_t2 1 1 2 n 7 (by decide) (by decide) (by decide)
      (by omega) (by decide) (by omega)

/-- The 7-forcing hypothesis produces actual positive natural denominators. -/
theorem t2_seven_covered (s : ℕ) (hleg : legendreSym 7 (s : ℤ) = -1) :
    ESCovering.Covered s := qnr7_covered s (legendre_seven_neg_one s hleg)

/-- Entire progressions with a modulus divisible by 20 inherit 5-forcing
coverage; no positivity exception at t=0 is omitted. -/
theorem t1_five_covers_class (M s : ℕ) (hM : 20 ∣ M) (h4 : s%4 = 1)
    (hleg : legendreSym 5 (s : ℤ) = -1) : ESCovering.CoversClass M s := by
  intro t
  have hmod : (M*t+s)%20 = s%20 := by
    simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hM]
  obtain ⟨f, hf, hclass⟩ := t1_five_forcing_full s h4 hleg
  exact t1_w20_class_covered (M*t+s) f hf (hmod.trans hclass)

/-- Entire progressions with a modulus divisible by 7 inherit T2 coverage. -/
theorem t2_seven_covers_class (M s : ℕ) (hM : 7 ∣ M)
    (hleg : legendreSym 7 (s : ℤ) = -1) : ESCovering.CoversClass M s := by
  intro t
  have hmod : (M*t+s)%7 = s%7 := by
    simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hM]
  apply qnr7_covered
  rw [hmod]
  exact legendre_seven_neg_one s hleg

end ESFiveSevenForcing
