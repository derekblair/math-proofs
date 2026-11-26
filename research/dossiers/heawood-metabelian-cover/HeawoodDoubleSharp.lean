import HeawoodDoubleNonabel
import HeawoodLift64Witness
import Mathlib.GroupTheory.Solvable

namespace HeawoodDouble
open HaarDerivedFlowPositive
open HeawoodDoubleDeck
open scoped commutatorElement

theorem deck_class_two : derivedSeries Deck 2 = ⊥ ∧ derivedSeries Deck 1 ≠ ⊥ := by
  refine ⟨?_, by simpa only [derivedSeries_one] using commutator_nontrivial⟩
  rw [show (2:ℕ)=1+1 by decide,derivedSeries_succ,derivedSeries_one,eq_bot_iff]
  apply Subgroup.commutator_le.mpr
  intro a ha b hb
  apply Subgroup.mem_bot.mpr
  apply commutatorElement_eq_one_iff_mul_comm.mpr
  exact congrArg Subtype.val (metabelian ⟨a,ha⟩ ⟨b,hb⟩)

theorem smallest_dyadic :
    Cyclic Edge2 64 ∧ ∀ n ∈ [4,8,16,32], ¬ Cyclic Edge2 n := by
  refine ⟨HeawoodLift64.cycle64,?_⟩
  intro n hn h
  have c := second_lower n (by simp at hn;omega) h
  simp at hn
  omega

/-- The two successive full all-edge mod-3 voltage lifts of Heawood
form a finite regular cover with a metabelian, nonabelian deck group.
Its ordinary girth is 54 and its least dyadic simple cycle length is 64. -/
theorem verified_example :
    Odd (Nat.card Deck) ∧ derivedSeries Deck 2=⊥ ∧ derivedSeries Deck 1≠⊥ ∧
    (Cyclic Edge2 54 ∧ ∀ n, 3≤n → Cyclic Edge2 n → 54≤n) ∧
    (Cyclic Edge2 64 ∧ ∀ n ∈ [4,8,16,32], ¬ Cyclic Edge2 n) :=
  ⟨finite_odd,deck_class_two.1,deck_class_two.2,girth54,smallest_dyadic⟩

end HeawoodDouble
#print axioms HeawoodDouble.verified_example
