import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

namespace HaarMetaSmallAffine

/-- Set equivalence of three residues under a unit affine map of the cyclic group. -/
def Affine (n : ℕ) (x y u v : ℕ) : Prop :=
  ∃ (a b : Fin n), Nat.gcd a.val n = 1 ∧ ∀ c : Fin n,
    (c.val = b.val ∨ c.val = (a.val * x + b.val) % n ∨ c.val = (a.val * y + b.val) % n) ↔
      (c.val = 0 ∨ c.val = u ∨ c.val = v)

private instance (n x y u v : ℕ) : Decidable (Affine n x y u v) :=
  inferInstanceAs (Decidable (∃ (a b : Fin n), Nat.gcd a.val n = 1 ∧ ∀ c : Fin n,
    (c.val = b.val ∨ c.val = (a.val * x + b.val) % n ∨ c.val = (a.val * y + b.val) % n) ↔
      (c.val = 0 ∨ c.val = u ∨ c.val = v)))

def Distinct (n x y : ℕ) : Prop :=
  x % n ≠ 0 ∧ y % n ≠ 0 ∧ x % n ≠ y % n

private instance (n x y : ℕ) : Decidable (Distinct n x y) :=
  inferInstanceAs (Decidable (x % n ≠ 0 ∧ y % n ≠ 0 ∧ x % n ≠ y % n))

def primitivePattern (q : Fin 3) : ℕ × ℕ × ℕ :=
  ![(1,3,10), (1,4,12), (2,5,13)] q

/-- Finite checks for the primitive integer patterns (1,3), (1,4), (2,5).
The bounds are respectively 10, 12, 13 (exclusive). -/
theorem primitive (q : Fin 3) (n : Fin 13) :
    3 ≤ n.val → n.val % 2 = 1 → n.val < (primitivePattern q).2.2 →
      Distinct n.val (primitivePattern q).1 (primitivePattern q).2.1 →
      Affine n.val (primitivePattern q).1 (primitivePattern q).2.1 1 2 ∨
        ((n.val = 7 ∨ n.val = 9 ∨ n.val = 11) ∧
          Affine n.val (primitivePattern q).1 (primitivePattern q).2.1 1 3) := by
  fin_cases q <;> fin_cases n <;> decide

def NonzeroThreeOrderGenerators (n t z : ℕ) : Prop :=
  Nat.gcd (Nat.gcd t z) n = 1 ∧ t ≠ 0 ∧ 3*t % n = 0

private instance (n t z : ℕ) : Decidable (NonzeroThreeOrderGenerators n t z) :=
  inferInstanceAs (Decidable (Nat.gcd (Nat.gcd t z) n = 1 ∧ t ≠ 0 ∧ 3*t % n = 0))

theorem torsion9_pair (t z : Fin 9) :
    NonzeroThreeOrderGenerators 9 t.val z.val → Distinct 9 t.val z.val →
      Affine 9 t.val z.val 1 3 := by decide +revert

theorem torsion9_shift (t z : Fin 9) :
    NonzeroThreeOrderGenerators 9 t.val z.val → Distinct 9 z.val (2*z.val+t.val) →
      Affine 9 z.val (2*z.val+t.val) 1 2 := by decide +revert

theorem torsion15_shift (t z : Fin 15) :
    NonzeroThreeOrderGenerators 15 t.val z.val → Distinct 15 z.val (2*z.val+t.val) →
      Affine 15 z.val (2*z.val+t.val) 1 3 ∨ Affine 15 z.val (2*z.val+t.val) 1 4 := by decide +revert

#print axioms primitive
#print axioms torsion9_pair
#print axioms torsion9_shift
#print axioms torsion15_shift
end HaarMetaSmallAffine
