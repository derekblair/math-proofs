import FreeSite
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace IU.Lubell
open Nat
open scoped BigOperators

def weight (n k : Nat) : ℚ :=
  ((k.factorial : ℚ) * ((n-k).factorial : ℚ)) / ((n+1).factorial : ℚ)

def score (n : Nat) (F : Finset (Finset Nat)) : ℚ :=
  ∑ A ∈ F, weight n A.card

theorem score_normalized {n k : Nat} (h : k≤n) :
    weight n k = 1 / (((n+1 : Nat) : ℚ) * (n.choose k : ℚ)) := by
  unfold weight
  rw [Nat.factorial_succ n]
  have p : 0 < (n.choose k : ℚ) := by exact_mod_cast Nat.choose_pos h
  have f : 0 < (n.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos _
  have q := Nat.choose_mul_factorial_mul_factorial h
  have Q : (n.choose k : ℚ) * (k.factorial : ℚ) * ((n-k).factorial : ℚ) =
      (n.factorial : ℚ) := by exact_mod_cast q
  push_cast
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  linear_combination (n+1 : ℚ) * Q

theorem weight_extend {n k : Nat} (h : k≤n) :
    weight (n+1) k + weight (n+1) (k+1) = weight n k := by
  unfold weight
  rw [show n+1-k=n-k+1 by omega,show n+1-(k+1)=n-k by omega]
  rw [Nat.factorial_succ (n-k), Nat.factorial_succ k, Nat.factorial_succ (n+1)]
  push_cast
  rw [←add_div]
  have A : (n-k : Nat) + k=n := by omega
  have B : ((n-k : Nat) : ℚ)+(k:ℚ)=(n:ℚ) := by exact_mod_cast A
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  linear_combination ((k.factorial : Nat) : ℚ) * (((n-k).factorial : Nat) : ℚ) *
    (((n+1).factorial : Nat) : ℚ) * B

theorem score_extend {n p q : Nat} {F : Finset (Finset Nat)} (ok : IsIU F n p q) :
    score (n+1) (double F n)=score n F := by
  classical
  have no (A : Finset Nat) (h : A∈F) : n∉A :=
    fun z => Nat.lt_irrefl _ (Finset.mem_range.mp (ok.1 A h z))
  have inj : Set.InjOn (fun A : Finset Nat => insert n A) ↑F := by
    intro A a B b eq
    have E := congrArg (fun X : Finset Nat => X.erase n) eq
    simpa [Finset.erase_insert,no A a,no B b] using E
  have dis : Disjoint F (F.image (fun A => insert n A)) := Finset.disjoint_left.mpr (by
    intro A ha hb
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hb
    exact no _ ha (Finset.mem_insert_self _ _))
  unfold double score
  rw [Finset.sum_union dis,Finset.sum_image inj,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A a
  rw [Finset.card_insert_of_notMem (no A a)]
  exact weight_extend (by simpa using Finset.card_le_card (ok.1 A a))

#print axioms weight_extend
#print axioms score_extend
end IU.Lubell
