import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset
open scoped BigOperators
namespace SparseHalfGraphon

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def unorderedCost (W : V→V→ℝ) (s : Finset V) : ℝ :=
  (∑ x∈s,∑ y∈s,W x y)/2

lemma unorderedCost_insert (W : V→V→ℝ) (sym : ∀ x y, W x y=W y x)
    (loop : ∀ x, W x x=0) (S : Finset V) (v : V) (hv : v∉S) :
    unorderedCost W (insert v S)=unorderedCost W S+∑ x∈S, W v x := by
  unfold unorderedCost
  rw [Finset.sum_insert hv,Finset.sum_insert hv,loop,zero_add]
  have he : (∑ x∈S,∑ y∈insert v S,W x y)=
      (∑ x∈S,W v x)+(∑ x∈S,∑ y∈S,W x y) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_insert hv,sym x v]
  rw [he]
  ring

/-- Razborov's greedy growth can be expressed as a maximal feasible
finite set. If it stops below the goal, every remaining degree exceeds
the growth budget. -/
theorem finite_greedy_growth (W : V→V→ℝ) (sym : ∀ x y, W x y=W y x)
    (loop : ∀ x, W x x=0) (A : Finset V) (hA : unorderedCost W A=0)
    (m : ℕ) (hm : A.card≤m) (r : ℝ) :
    ∃ B : Finset V, A⊆B ∧ B.card≤m ∧
      unorderedCost W B≤r*((B.card:ℝ)-(A.card:ℝ)) ∧
      (B.card=m ∨ ∀ v∉B, r<∑ x∈B,W v x) := by
  classical
  let feasible (B : Finset V) : Prop := A⊆B ∧ B.card≤m ∧
    unorderedCost W B≤r*((B.card:ℝ)-(A.card:ℝ))
  let pool := (Finset.univ : Finset (Finset V)).filter feasible
  have ha : A ∈ pool := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,subset_rfl,hm,?_⟩
    simp [hA]
  obtain ⟨B,hB,hmax⟩ := exists_max_image pool Finset.card ⟨A,ha⟩
  obtain ⟨hAB,hBm,hBcost⟩ := (Finset.mem_filter.mp hB).2
  refine ⟨B,hAB,hBm,hBcost,?_⟩
  by_cases ht : B.card=m
  · exact Or.inl ht
  · right
    intro v hv
    by_contra! hdeg
    have hBi : insert v B ∈ pool := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,hAB.trans (Finset.subset_insert _ _),?_,?_⟩
      · rw [Finset.card_insert_of_notMem hv]
        omega
      · rw [unorderedCost_insert W sym loop B v hv,Finset.card_insert_of_notMem hv]
        push_cast
        linarith
    have h := hmax (insert v B) hBi
    rw [Finset.card_insert_of_notMem hv] at h
    omega

#print axioms finite_greedy_growth
end SparseHalfGraphon
