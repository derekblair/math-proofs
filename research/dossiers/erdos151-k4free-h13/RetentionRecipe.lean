import RamseySmall
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs

namespace Erdos151H13

/-- Conservative independence guarantees using only the Ramsey bounds
at one, three and six vertices. No unverified numerical input. -/
def alphaFloor (n : ℕ) : ℕ :=
  if 6 ≤ n then 3 else if 3 ≤ n then 2 else if 1 ≤ n then 1 else 0

theorem choose_alpha_floor {V : Type*} [Fintype V] [DecidableEq V]
    (G : V → V → Prop) [DecidableRel G] (S : Finset V) (m : ℕ) (h : m ≤ S.card)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (tf : Erdos151Ramsey.TriangleFree G) :
    ∃ T ⊆ S, alphaFloor m ≤ T.card ∧ Erdos151Ramsey.Independent G T := by
  unfold alphaFloor
  split
  · exact Erdos151Ramsey.independent_three_of_six G sym irr tf S (by omega)
  split
  · exact Erdos151Ramsey.independent_two_of_three G sym irr tf S (by omega)
  split
  · obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
    exact ⟨{a},Finset.singleton_subset_iff.mpr ha,by simp,by simpa [Erdos151Ramsey.Independent] using (irr a)⟩
  · exact ⟨∅,Finset.empty_subset _,by simp,by simp [Erdos151Ramsey.Independent]⟩

/-- Elementary check of the thin-overlap arithmetic. Only (4,4,1)
needs the stronger shared-point three-vertex outer guarantee. -/
theorem thin_overlap_recipe (a b s t : ℕ)
    (a4 : 4 ≤ a) (b3 : 3 ≤ b) (mix : 4 ≤ b ∨ 2 ≤ t)
    (thin : a+b+s < 10) :
    let center := alphaFloor (7+t-a-b)
    let union := alphaFloor (14-a-b-s)
    let separated := alphaFloor (7-a-s)+alphaFloor (7-b-s)
    12 ≤ a+b+s+center+union ∨
    12 ≤ a+b+s+center+separated ∨ (a=4 ∧ b=4 ∧ s=1) := by
  have a6 : a ≤ 6 := by omega
  have b5 : b ≤ 5 := by omega
  have s2 : s ≤ 2 := by omega
  interval_cases a <;> interval_cases b <;> interval_cases s <;>
    simp [alphaFloor] at * <;> (try split_ifs) <;> omega

#print axioms choose_alpha_floor
#print axioms thin_overlap_recipe
end Erdos151H13
