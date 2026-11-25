import Mathlib.Data.Nat.Choose.Basic

/-!
# Rule 126 space-time closed form

Standalone M1 helpers for the frozen Rule 129 dossier. The local rule and
global step repeat the locked definitions, without importing the pinned module.
-/

namespace Mathproofs.Rule129ClosedForm

/-- Wolfram's local rule, with the locked bit encoding. -/
def ecaRule (R : Nat) (p q r : Bool) : Bool :=
  R.testBit (4 * p.toNat + 2 * q.toNat + r.toNat)

/-- One synchronous step on the infinite integer lattice. -/
def ecaStep (R : Nat) (c : Int → Bool) : Int → Bool :=
  fun x => ecaRule R (c (x - 1)) (c x) (c (x + 1))

/-- The guarded binomial-parity closed form from dossier §2.3. -/
def B (n : Nat) (x : Int) : Bool :=
  if x.natAbs ≤ n then Nat.choose n ((n - x.natAbs) / 2) % 2 == 1 else false

theorem rule126_fff : ecaRule 126 false false false = false := rfl
theorem rule126_tff : ecaRule 126 true false false = true := rfl
theorem rule126_ttf : ecaRule 126 true true false = true := rfl
theorem rule126_ftf : ecaRule 126 false true false = true := rfl

theorem rule126_symm (p q r : Bool) :
    ecaRule 126 r q p = ecaRule 126 p q r := by
  cases p <;> cases q <;> cases r <;> rfl

theorem rule126_eq_bne_left (a b : Bool) : ecaRule 126 a a b = (a != b) := by
  cases a <;> cases b <;> rfl

theorem rule126_eq_bne_right (a b : Bool) : ecaRule 126 a b b = (a != b) := by
  cases a <;> cases b <;> rfl

theorem rule126_eq_bne_outer (a b : Bool) : ecaRule 126 a b a = (a != b) := by
  cases a <;> cases b <;> rfl

theorem rule126_same (a : Bool) : ecaRule 126 a a a = false := by
  cases a <;> rfl


theorem choose_succ_mod_two_bne (n j : Nat) :
    (Nat.choose (n + 1) (j + 1) % 2 == 1) =
      ((Nat.choose n (j + 1) % 2 == 1) != (Nat.choose n j % 2 == 1)) := by
  rw [Nat.choose_succ_succ', Nat.add_mod]
  rcases Nat.mod_two_eq_zero_or_one (Nat.choose n j) with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one (Nat.choose n (j + 1)) with h' | h' <;>
      simp only [h, h'] <;> rfl

theorem choose_central_even (k : Nat) :
    (Nat.choose (2 * k + 2) (k + 1) % 2 == 1) = false := by
  change (Nat.choose ((2 * k + 1) + 1) (k + 1) % 2 == 1) = false
  rw [Nat.choose_succ_succ', Nat.choose_symm_half, Nat.add_mod]
  rcases Nat.mod_two_eq_zero_or_one (Nat.choose (2 * k + 1) k) with h | h <;>
    simp only [h] <;> rfl


theorem B_zero_eq_singleSeed (x : Int) : B 0 x = (x == 0) := by
  by_cases hx : x = 0 <;> simp [B, hx]

theorem B_neg (n : Nat) (x : Int) : B n (-x) = B n x := by
  simp only [B, Int.natAbs_neg]

theorem B_ofNat (n m : Nat) :
    B n (m : Int) = if m ≤ n then Nat.choose n ((n - m) / 2) % 2 == 1 else false := by
  rfl

theorem B_ofNat_inside (n m : Nat) (h : m ≤ n) :
    B n (m : Int) = (Nat.choose n ((n - m) / 2) % 2 == 1) := by
  rw [B_ofNat, ite_eq_left h]

theorem B_ofNat_outside (n m : Nat) (h : n < m) : B n (m : Int) = false := by
  rw [B_ofNat, ite_eq_right (by omega)]

/-- At a positive site, all three arguments can be written as natural casts. -/
theorem step_ofNat_succ (n m : Nat) :
    ecaStep 126 (B n) ((m + 1 : Nat) : Int) =
      ecaRule 126 (B n (m : Int)) (B n ((m + 1 : Nat) : Int))
        (B n ((m + 2 : Nat) : Int)) := by
  have hl : ((m + 1 : Nat) : Int) - 1 = (m : Int) := by omega
  have hr : ((m + 1 : Nat) : Int) + 1 = ((m + 2 : Nat) : Int) := by omega
  rw [ecaStep, hl, hr]

theorem B_frontier (n : Nat) : B n (n : Int) = true := by
  simp [B_ofNat]

/-- Regime 1: beyond the next light cone, all inputs and the output vanish. -/
theorem step126_B_far (n m : Nat) (h : n + 2 ≤ m) :
    ecaStep 126 (B n) (m : Int) = B (n + 1) (m : Int) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [step_ofNat_succ, B_ofNat_outside n k (by omega),
    B_ofNat_outside n (k + 1) (by omega), B_ofNat_outside n (k + 2) (by omega),
    B_ofNat_outside (n + 1) (k + 1) (by omega), rule126_fff]

/-- Regime 2: the newly reached site sees precisely its inner neighbor. -/
theorem step126_B_next (n : Nat) :
    ecaStep 126 (B n) ((n + 1 : Nat) : Int) =
      B (n + 1) ((n + 1 : Nat) : Int) := by
  rw [step_ofNat_succ, B_frontier,
    B_ofNat_outside n (n + 1) (by omega), B_ofNat_outside n (n + 2) (by omega),
    B_frontier, rule126_tff]

/-- Regime 3: the old positive frontier has two ON inputs. -/
theorem step126_B_edge (n : Nat) (h : 1 ≤ n) :
    ecaStep 126 (B n) (n : Int) = B (n + 1) (n : Int) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hin : B (k + 1) (k : Int) = true := by
    rw [B_ofNat_inside (k + 1) k (by omega)]
    simp
  have hout : B (k + 1 + 1) ((k + 1 : Nat) : Int) = true := by
    rw [B_ofNat_inside (k + 1 + 1) (k + 1) (by omega)]
    simp
  rw [step_ofNat_succ, hin, B_frontier,
    B_ofNat_outside (k + 1) (k + 2) (by omega), hout, rule126_ttf]


/-- Regime 4: the two parities of the interior floor indices reduce to Pascal. -/
theorem step126_B_interior (n m' : Nat) (h : m' + 2 ≤ n) :
    ecaStep 126 (B n) (↑(m' + 1)) = B (n + 1) (↑(m' + 1)) := by
  have hl : ((m' + 1 : Nat) : Int) - 1 = (m' : Int) := by omega
  have hr : ((m' + 1 : Nat) : Int) + 1 = ((m' + 2 : Nat) : Int) := by omega
  simp only [ecaStep, hl, hr]
  rw [B_ofNat_inside n m' (by omega), B_ofNat_inside n (m' + 1) (by omega),
    B_ofNat_inside n (m' + 2) h, B_ofNat_inside (n + 1) (m' + 1) (by omega)]
  let u := n - (m' + 2)
  have hleft : n - m' = u + 2 := by omega
  have hmid : n - (m' + 1) = u + 1 := by omega
  have htarget : n + 1 - (m' + 1) = u + 2 := by omega
  rw [hleft, hmid, htarget]
  change ecaRule 126
    (Nat.choose n ((u + 2) / 2) % 2 == 1)
    (Nat.choose n ((u + 1) / 2) % 2 == 1)
    (Nat.choose n (u / 2) % 2 == 1) =
    (Nat.choose (n + 1) ((u + 2) / 2) % 2 == 1)
  obtain ⟨j, hj | hj⟩ : ∃ j : Nat, u = 2 * j ∨ u = 2 * j + 1 := by
    exact ⟨u / 2, by omega⟩
  · have hdiv0 : (2 * j) / 2 = j := by omega
    have hdiv1 : (2 * j + 1) / 2 = j := by omega
    have hdiv2 : (2 * j + 2) / 2 = j + 1 := by omega
    rw [hj, hdiv0, hdiv1, hdiv2, rule126_eq_bne_right,
      ← choose_succ_mod_two_bne]
  · have hdiv1 : (2 * j + 1) / 2 = j := by omega
    have hdiv2 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    have hdiv3 : (2 * j + 1 + 2) / 2 = j + 1 := by omega
    rw [hj, hdiv1, hdiv2, hdiv3, rule126_eq_bne_left,
      ← choose_succ_mod_two_bne]

theorem bne_comm (a b : Bool) : (a != b) = (b != a) := by
  cases a <;> cases b <;> rfl

/-- Regime 5: at the origin, split zero, positive even, and odd generations. -/
theorem step126_B_zero (n : Nat) : ecaStep 126 (B n) 0 = B (n + 1) 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
      have hdiv : (2 * k) / 2 = k := by omega
      have hdiv' : (2 * k + 1) / 2 = k := by omega
      have hdiv'' : (2 * k + 2) / 2 = k + 1 := by omega
      simp only [ecaStep, B, show ((0 : Int) - 1).natAbs = 1 from rfl,
        show (0 : Int).natAbs = 0 from rfl,
        show ((0 : Int) + 1).natAbs = 1 from rfl]
      simp only [show 1 ≤ (2 * k).succ from by omega, Nat.zero_le,
        ite_true, Nat.sub_zero, show (2 * k).succ - 1 = 2 * k from by omega,
        hdiv, hdiv', hdiv'', rule126_same, choose_central_even]
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
      have hdiv : (2 * k + 1) / 2 = k := by omega
      have hdiv' : (2 * k + 2) / 2 = k + 1 := by omega
      have hdiv'' : (2 * k + 3) / 2 = k + 1 := by omega
      simp only [ecaStep, B, show ((0 : Int) - 1).natAbs = 1 from rfl,
        show (0 : Int).natAbs = 0 from rfl,
        show ((0 : Int) + 1).natAbs = 1 from rfl]
      simp only [show 1 ≤ (2 * k + 1).succ from by omega, Nat.zero_le,
        ite_true, Nat.sub_zero, show (2 * k + 1).succ - 1 = 2 * k + 1 from by omega,
        show 2 * k + 1 + 1 = 2 * k + 2 from by omega,
        show 2 * k + 2 + 1 = 2 * k + 3 from by omega, hdiv, hdiv', hdiv'',
        rule126_eq_bne_outer]
      exact (bne_comm _ _).trans (choose_succ_mod_two_bne (2 * k + 2) k).symm

/-- The nonnegative half-line, partitioned into the five dossier regimes. -/
theorem step126_B_ofNat (n m : Nat) :
    ecaStep 126 (B n) (m : Int) = B (n + 1) (m : Int) := by
  by_cases hfar : n + 2 ≤ m
  · exact step126_B_far n m hfar
  by_cases hnext : m = n + 1
  · subst m
    exact step126_B_next n
  by_cases hedge : m = n ∧ 1 ≤ n
  · obtain ⟨hm, hn⟩ := hedge
    subst m
    exact step126_B_edge n hn
  by_cases hpos : 0 < m
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact step126_B_interior n m' (by omega)
  · have hm : m = 0 := by omega
    subst m
    exact step126_B_zero n

/-- Reflection reverses the neighbors; Rule 126 is left-right symmetric. -/
theorem step126_reflect_B (n : Nat) (x : Int) :
    ecaStep 126 (B n) (-x) = ecaStep 126 (B n) x := by
  have hl : -x - 1 = -(x + 1) := by omega
  have hr : -x + 1 = -(x - 1) := by omega
  simp only [ecaStep, hl, hr, B_neg]
  exact rule126_symm _ _ _

/-- One synchronous Rule 126 step preserves the closed form for all integer sites. -/
theorem step126_B (n : Nat) (x : Int) :
    ecaStep 126 (B n) x = B (n + 1) x := by
  by_cases hx : 0 ≤ x
  · obtain ⟨m, rfl⟩ : ∃ m : Nat, x = (m : Int) := ⟨x.toNat, by omega⟩
    exact step126_B_ofNat n m
  · obtain ⟨m, hm⟩ : ∃ m : Nat, -x = (m : Int) := ⟨(-x).toNat, by omega⟩
    calc
      ecaStep 126 (B n) x = ecaStep 126 (B n) (-x) := (step126_reflect_B n x).symm
      _ = B (n + 1) (-x) := by rw [hm]; exact step126_B_ofNat n m
      _ = B (n + 1) x := B_neg (n + 1) x

end Mathproofs.Rule129ClosedForm
