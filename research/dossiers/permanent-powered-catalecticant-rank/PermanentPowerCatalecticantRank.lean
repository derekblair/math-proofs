import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fintype.Powerset

open scoped BigOperators

namespace PermanentPowerCatalecticant

/-- A rectangular matrix with disjoint, nonempty constant blocks has
    one unit of rank per nonzero block. -/
theorem constant_block_rank {K α β γ : Type*}
    [Field K] [Fintype α] [Fintype β] [Fintype γ]
    (f : α → γ) (g : β → γ) (c : γ → K)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hc : ∀ i, c i ≠ 0) :
    letI : DecidableEq γ := Classical.decEq γ
    (show Matrix α β K from fun i j => if f i = g j then c (f i) else 0).rank =
      Fintype.card γ := by
  classical
  let D : Matrix α β K := fun i j => if f i = g j then c (f i) else 0
  change D.rank = Fintype.card γ
  let L : Matrix α γ K := fun i k => if k = f i then c k else 0
  let R : Matrix γ β K := fun k j => if k = g j then 1 else 0
  have hfac : L * R = D := by
    ext i j
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (f i)]
    · by_cases h : f i = g j <;> simp [L, R, D, h]
    · intro k _ hk
      simp [L, hk]
    · simp
  have hup : D.rank ≤ Fintype.card γ := by
    rw [← hfac]
    exact (Matrix.rank_mul_le_left L R).trans (Matrix.rank_le_card_width L)
  let rf : γ → α := fun k => Classical.choose (hf k)
  let rg : γ → β := fun k => Classical.choose (hg k)
  have hrf (k : γ) : f (rf k) = k := Classical.choose_spec (hf k)
  have hrg (k : γ) : g (rg k) = k := Classical.choose_spec (hg k)
  have hsub : D.submatrix rf rg = Matrix.diagonal c := by
    ext k l
    change (if f (rf k) = g (rg l) then c (f (rf k)) else 0) = _
    rw [hrf, hrg, Matrix.diagonal_apply]
  have hdiag : (Matrix.diagonal c).rank = Fintype.card γ := by
    rw [Matrix.rank_diagonal]
    exact Fintype.card_congr {
      toFun := Subtype.val
      invFun := fun k => ⟨k, hc k⟩
      left_inv := fun ⟨k, _⟩ => rfl
      right_inv := fun _ => rfl
    }
  apply le_antisymm hup
  rw [← hdiag, ← hsub]
  exact Matrix.rank_submatrix_le D rf rg

/-- Rank bound once a coefficient matrix has been separated through
    a summand index and two independent fixed-cardinality subsets. -/
theorem minor_feature_rank_bound {K α β : Type*} [Field K] [Fintype α] [Fintype β]
    (m M k : ℕ)
    (A : Matrix α (Fin m × ({s : Finset (Fin M) // s.card = k} ×
                            {s : Finset (Fin M) // s.card = k})) K)
    (B : Matrix (Fin m × ({s : Finset (Fin M) // s.card = k} ×
                          {s : Finset (Fin M) // s.card = k})) β K) :
    (A * B).rank ≤ m * (M.choose k)^2 := by
  refine (Matrix.rank_mul_le_left A B).trans ?_
  simpa [Fintype.card_finset_len, pow_two] using Matrix.rank_le_card_width A

#print axioms constant_block_rank
#print axioms minor_feature_rank_bound

end PermanentPowerCatalecticant
