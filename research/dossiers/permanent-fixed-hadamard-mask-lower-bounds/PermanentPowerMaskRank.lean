import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Tactic

open scoped BigOperators

namespace PermanentPowerMask

/-- Factorizing the full matching identity through m weighted masks needs
    at least n! intermediary coordinates. This is the rank step, separate
    from obtaining the identity by matching polynomial coefficients. -/
theorem matching_identity_mask_count
    {K : Type*} [Field K] (n m q : ℕ)
    (w : Fin m → K) (v : Fin m → Equiv.Perm (Fin n) → K)
    (h : ∀ σ τ : Equiv.Perm (Fin n),
      (∑ i, w i * (v i σ)^(q-1) * v i τ) =
        if σ = τ then 1 else 0) :
    n.factorial ≤ m := by
  classical
  let A : Matrix (Equiv.Perm (Fin n)) (Fin m) K := fun σ i => w i * (v i σ)^(q-1)
  let B : Matrix (Fin m) (Equiv.Perm (Fin n)) K := fun i τ => v i τ
  have hid : A * B = 1 := by
    ext σ τ
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact h σ τ
  calc
    n.factorial = (1 : Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) K).rank := by
      simp [Matrix.rank_one, Fintype.card_perm]
    _ = (A * B).rank := by rw [hid]
    _ ≤ A.rank := Matrix.rank_mul_le_left A B
    _ ≤ m := by simpa using Matrix.rank_le_card_width A

#print axioms matching_identity_mask_count


/-- Rank step for tensorized local lifts of width q, expanded over all
    choices of one coordinate per block. -/
theorem block_factor_rank_bound
    {K α : Type*} [Field K] [Fintype α] [DecidableEq α] (m q r : ℕ)
    (A : Matrix α (Fin m × (Fin r → Fin q)) K)
    (B : Matrix (Fin m × (Fin r → Fin q)) α K)
    (h : A * B = 1) :
    Fintype.card α ≤ m * q^r := by
  calc
    Fintype.card α = (1 : Matrix α α K).rank := by simp [Matrix.rank_one]
    _ = (A * B).rank := by rw [h]
    _ ≤ A.rank := Matrix.rank_mul_le_left A B
    _ ≤ m * q^r := by simpa [Fintype.card_fun] using Matrix.rank_le_card_width A

/-- The local middle coefficient of a complex modulus power is positive
    for a nonzero cycle ratio when q ≥ 2. -/
theorem local_modulus_middle_coeff {x y q : ℝ} (hq : 1 ≤ q) :
    q * (x^2+y^2) ≤ q*(q-1)*(x^2-y^2) + q^2*(x^2+y^2) := by
  have hq' : 0 ≤ q * (q - 1) := mul_nonneg (by linarith) (by linarith)
  nlinarith only [mul_nonneg hq' (sq_nonneg x)]

#print axioms block_factor_rank_bound
#print axioms local_modulus_middle_coeff

end PermanentPowerMask
