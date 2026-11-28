import Mathlib.Data.List.Range
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Monotone.Basic

namespace Erdos151N63

/-- Exact finite arrays, represented as Fin-indexed functions so the
enumerator cannot accidentally omit any fixed-width input. -/
def tuples (q : Nat) : (d : Nat) → List (Fin d → Fin q)
  | 0 => [Fin.elim0]
  | d+1 => (List.finRange q).flatMap fun h =>
      (tuples q d).map (fun t => Fin.cases h t)

theorem mem_tuples (q d : Nat) (f : Fin d → Fin q) : f ∈ tuples q d := by
  induction d with
  | zero =>
    change f ∈ [Fin.elim0]
    exact List.mem_singleton.mpr (funext (fun j => Fin.elim0 j))
  | succ d ih =>
    simp only [tuples, List.mem_flatMap,List.mem_map]
    refine ⟨f 0,List.mem_finRange _,(fun i => f i.succ),ih _,?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl

/-- Filtering an exhaustive finite tuple list preserves exactly those
inputs satisfying a certified Boolean condition. -/
theorem mem_filter_tuples (q d : Nat) (f : Fin d → Fin q)
    (P : (Fin d → Fin q) → Bool) (h : P f = true) :
    f ∈ (tuples q d).filter P :=
  List.mem_filter.mpr ⟨mem_tuples q d f,h⟩

#print axioms mem_filter_tuples

/-- Extend a monotone tuple one coordinate at a time, pruning values
below the previous coordinate and values outside a fixed mask bank. -/
def monotoneTuples (q : Nat) (allowed : Fin q → Bool) :
    (d : Nat) → Nat → List (Fin d → Fin q)
  | 0, _ => [Fin.elim0]
  | d+1, lo => ((List.finRange q).filter fun h => lo ≤ h.val && allowed h).flatMap
      fun h => (monotoneTuples q allowed d h.val).map (fun t => Fin.cases h t)

theorem mem_monotoneTuples (q : Nat) (allowed : Fin q → Bool)
    (d : Nat) (lo : Nat) (f : Fin d → Fin q)
    (mono : ∀ i j : Fin d, i.val ≤ j.val → (f i).val ≤ (f j).val) (hl : ∀ i, lo ≤ (f i).val)
    (ha : ∀ i, allowed (f i) = true) :
    f ∈ monotoneTuples q allowed d lo := by
  induction d generalizing lo with
  | zero =>
    change f ∈ [Fin.elim0]
    exact List.mem_singleton.mpr (funext (fun j => Fin.elim0 j))
  | succ d ih =>
    simp only [monotoneTuples, List.mem_flatMap,List.mem_map]
    refine ⟨f 0,List.mem_filter.mpr ⟨List.mem_finRange _,by simp [hl,ha]⟩,
      (fun i => f i.succ),?_,?_⟩
    · apply ih
      · exact fun i j h => mono i.succ j.succ (Nat.succ_le_succ h)
      · exact fun i => mono 0 i.succ (Nat.zero_le _)
      · exact fun i => ha i.succ
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl

#print axioms mem_monotoneTuples
end Erdos151N63
