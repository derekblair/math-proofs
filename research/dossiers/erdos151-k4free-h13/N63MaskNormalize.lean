import N63NormalizeShape
import Mathlib.Data.Fin.Tuple.Sort
import Init.Data.BitVec.Lemmas

namespace Erdos151N63
open scoped BigOperators

def bitsOf : (n : Nat) → (Fin n → Bool) → BitVec n
  | 0, _ => 0
  | n+1, f => (bitsOf n (fun i => f i.succ)).concat (f 0)

theorem bitsOf_reads (n : Nat) (f : Fin n → Bool) (i : Fin n) :
    (bitsOf n f).toNat.testBit i.val = f i := by
  rw [BitVec.testBit_toNat]
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [bitsOf]
      exact BitVec.getLsbD_concat_zero
    · simp only [bitsOf, Fin.val_succ, BitVec.getLsbD_concat_succ]
      exact ih (fun i => f i.succ) j

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : V → V → Prop) [DecidableRel G]

/-- The row masks can be sorted without altering any graph edge: permute
only the independent neighbor block of the chosen pivot. -/
theorem max_normalization_sorted (n : Nat) (hn : Fintype.card V = n)
    (hd : 3*n < ∑ v : V, fullDeg G v)
    (irr : ∀ v, ¬ G v v)
    (tf : ∀ w x y, G w x → G w y → ¬G x y) :
    ∃ w : V, 4 ≤ fullDeg G w ∧ fullDeg G w+1 ≤ n ∧
      (∀ v : V, fullDeg G v ≤ fullDeg G w) ∧
      ∃ L : Fin (fullDeg G w) ≃ {z : V // G w z},
      ∃ R : Fin (n-1-fullDeg G w) ≃ {z : V // z ≠ w ∧ ¬G w z},
      ∃ M : Fin (fullDeg G w) → Nat,
        Monotone M ∧ (∀ i, M i < 2^(n-1-fullDeg G w)) ∧
        (∀ i j, (M i).testBit j.val = true ↔ G (L i).val (R j).val) ∧
        (∀ i j, ¬G (L i).val (L j).val) ∧
        ∀ z : V, z = w ∨ (∃ i, (L i).val = z) ∨ (∃ j, (R j).val = z) := by
  obtain ⟨w,h4,hwn,hm,L,R,hL,cover⟩ := max_normalization_blocks G n hn hd irr tf
  let q := n-1-fullDeg G w
  let B (i : Fin (fullDeg G w)) := bitsOf q (fun j => decide (G (L i).val (R j).val))
  let M (i : Fin (fullDeg G w)) := (B i).toNat
  let σ := Tuple.sort M
  refine ⟨w,h4,hwn,hm,σ.trans L,R,M ∘ σ, Tuple.monotone_sort M,?_,?_,?_,?_⟩
  · intro i
    exact (B (σ i)).isLt
  · intro i j
    change (B (σ i)).toNat.testBit j.val = true ↔ G (L (σ i)).val (R j).val
    rw [bitsOf_reads]
    simp
  · intro i j
    exact hL (σ i) (σ j)
  · intro z
    rcases cover z with h|⟨i,hi⟩|h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨σ.symm i,by simpa using hi⟩)
    · exact Or.inr (Or.inr h)

#print axioms bitsOf_reads
#print axioms max_normalization_sorted
end Erdos151N63
