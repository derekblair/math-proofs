import CriticalTransport
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace FolkmanB4.Tight
open Finset
variable {L V : Type*} [Fintype L] [Fintype V]

def bitZ (b : Bool) : Int := if b then 1 else 0

/-- A matcher's cut signing has fixed sum, depending only on the shore. -/
theorem signed_cut_balance (A : L → Bool) (B : V → Bool) (m : V ≃ L) :
    (∑ i : V, (bitZ (A (m i))-bitZ (B i))) =
      (∑ l : L, bitZ (A l))-(∑ i : V, bitZ (B i)) := by
  rw [sum_sub_distrib]
  exact congrArg (fun u : Int => u-(∑ i : V, bitZ (B i))) (Equiv.sum_comp m (fun l => bitZ (A l)))

/-- In a matching-covered bipartite graph all edges of a tight cut cross
in one bipartition direction. The conclusion records signed direction using
the two Boolean indicators for the chosen shore. -/
theorem one_cut_direction (I : L → V → Prop) (A : L → Bool) (B : V → Bool)
    (covered : ∀ l i, I l i → ∃ m : V ≃ L, m i=l ∧ ∀ j, I (m j) j)
    (tight : ∀ m : V ≃ L, (∀ j, I (m j) j) → ∃! j, A (m j)≠B j)
    {l k : L} {u w : V} (il : I l u) (ik : I k w)
    (cu : A l≠B u) (cw : A k≠B w) :
    bitZ (A l)-bitZ (B u) = bitZ (A k)-bitZ (B w) := by
  classical
  have step (l : L) (u : V) (i : I l u) (c : A l≠B u) :
      bitZ (A l)-bitZ (B u) =
        (∑ j : L, bitZ (A j))-(∑ j : V, bitZ (B j)) := by
    obtain ⟨m,ml,hm⟩ := covered l u i
    obtain ⟨j,hj,hu⟩ := tight m hm
    have ns : A (m u) ≠ B u := by simpa [ml] using c
    have e : j=u := (hu _ ns).symm
    have ss : (∑ x : V, (bitZ (A (m x))-bitZ (B x))) =
        bitZ (A (m u))-bitZ (B u) := by
      apply sum_eq_single u
      · intro y _ yne
        have eq : A (m y)=B y := by
          by_contra h
          exact yne ((hu _ h).trans e)
        simp [eq]
      · simp
    rw [ml] at ss
    exact ss.symm.trans (signed_cut_balance A B m)
  exact (step l u il cu).trans (step k w ik cw).symm

#print axioms one_cut_direction
end FolkmanB4.Tight
