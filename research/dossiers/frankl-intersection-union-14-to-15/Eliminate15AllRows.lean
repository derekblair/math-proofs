import Mathlib.Tactic.FinCases
import Eliminate15Rows0_2
import Eliminate15Rows0_3
import Eliminate15Rows0_4
import Eliminate15Rows0_5
import Eliminate15Rows0_6
import Eliminate15Rows0_7
import Eliminate15Rows0_8
import Eliminate15Rows0_9
import Eliminate15Rows0_10
import Eliminate15Rows0_11
import Eliminate15Rows0_12
import Eliminate15Rows0_13
import Eliminate15Rows1_5
import Eliminate15Rows1_6
import Eliminate15Rows1_7
import Eliminate15Rows1_8
import Eliminate15Rows1_9
import Eliminate15Rows1_10
import Eliminate15Rows1_11

namespace IU.IU15Tree
open IU.Eliminate
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem ofRows0 (k : Nat) : ∀ row∈maxRows 0 k, RowIsSound 0 k row := by
  by_cases hk : k<14
  · let j : Fin 14 := ⟨k,hk⟩
    change ∀ row∈maxRows 0 j.val, RowIsSound 0 j.val row
    clear_value j
    fin_cases j
    · intro row hr; cases (show row ∈ ([] : List (Row 4106)) from hr)
    · intro row hr; cases (show row ∈ ([] : List (Row 4106)) from hr)
    · exact rows0_2
    · exact rows0_3
    · exact rows0_4
    · exact rows0_5
    · exact rows0_6
    · exact rows0_7
    · exact rows0_8
    · exact rows0_9
    · exact rows0_10
    · exact rows0_11
    · exact rows0_12
    · exact rows0_13
  · obtain ⟨x, hx⟩ := Nat.exists_eq_add_of_le (show 14≤k by omega)
    subst k
    rw [show 14+x=x+14 by omega]
    intro row hr
    cases (show row∈([] : List (Row 4106)) from hr)
theorem ofRows1 (k : Nat) : ∀ row∈maxRows 1 k, RowIsSound 1 k row := by
  by_cases hk : k<14
  · let j : Fin 14 := ⟨k,hk⟩
    change ∀ row∈maxRows 1 j.val, RowIsSound 1 j.val row
    clear_value j
    fin_cases j
    · intro row hr; cases (show row ∈ ([] : List (Row 4106)) from hr)
    · intro row hr; cases (show row ∈ ([] : List (Row 4106)) from hr)
    · intro row hr; cases (show row ∈ ([] : List (Row 4106)) from hr)
    · intro row hr; cases (show row ∈ ([] : List (Row 4106)) from hr)
    · intro row hr; cases (show row ∈ ([] : List (Row 4106)) from hr)
    · exact rows1_5
    · exact rows1_6
    · exact rows1_7
    · exact rows1_8
    · exact rows1_9
    · exact rows1_10
    · exact rows1_11
    · intro row hr; cases (show row ∈ ([] : List (Row 4106)) from hr)
    · intro row hr; cases (show row ∈ ([] : List (Row 4106)) from hr)
  · obtain ⟨x, hx⟩ := Nat.exists_eq_add_of_le (show 14≤k by omega)
    subst k
    rw [show 14+x=x+14 by omega]
    intro row hr
    cases (show row∈([] : List (Row 4106)) from hr)
theorem allRows (s k : Nat) : ∀ row∈maxRows s k, RowIsSound s k row := by
  by_cases z : s=0
  · subst s; exact ofRows0 k
  by_cases o : s=1
  · subst s; exact ofRows1 k
  unfold maxRows
  rw [if_neg z,if_neg o]
  simp

theorem pivotFacts (k : Nat) (lo : 2≤k) (hi : k≤13) : PivotFacts k := by
  have H : ∀ j : Fin 14, 2≤j.val → PivotFacts j.val := by
    intro j
    fin_cases j
    · intro e; change 2≤0 at e; omega
    · intro e; change 2≤1 at e; omega
    · intro _; exact piv2
    · intro _; exact piv3
    · intro _; exact piv4
    · intro _; exact piv5
    · intro _; exact piv6
    · intro _; exact piv7
    · intro _; exact piv8
    · intro _; exact piv9
    · intro _; exact piv10
    · intro _; exact piv11
    · intro _; exact piv12
    · intro _; exact piv13
  exact H ⟨k,by omega⟩ lo
end IU.IU15Tree
