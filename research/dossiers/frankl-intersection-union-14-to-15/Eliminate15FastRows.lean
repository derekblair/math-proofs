import Eliminate15Structured

namespace IU.IU15Tree
open IU.Eliminate

def RowFast (s k : Nat) (row : Row 4106) : Prop :=
  pop row.a 15=k ∧ stage row.a=s ∧
  row.miss.Nodup ∧ 4106 - row.miss.length < 4092 ∧
  ∀ i∈row.miss, ∀ b∈colors i,
    b = row.a ∨ edgeFast 15 2 2 row.a b = false ∨ stage b < s

instance (s k : Nat) (row : Row 4106) : Decidable (RowFast s k row) := by
  unfold RowFast
  infer_instance

theorem row_fast_sound {s k : Nat} {row : Row 4106}
    (fast : RowFast s k row) : RowIsSound s k row := by
  obtain ⟨w,st,n,c,g⟩ := fast
  refine ⟨by simpa [pop_eq] using w, st,n,c,?_⟩
  intro i mi b bc
  rcases g i mi b bc with h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inr (by simpa [edge_fast] using h))
  · exact Or.inr (Or.inl (by simpa [st] using h))

end IU.IU15Tree
