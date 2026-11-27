import GeometricMomentEvents

namespace RobustFolkman.GeometricGap
open Finset
variable {V : Type*} [DecidableEq V] [Fintype V]

def tupleLabel (r : Tuple5 V) : Five→V
  | .inl (.inl i) => if i=0 then r.2.2.1 else r.2.2.2.1
  | .inl (.inr i) => if i=0 then r.1 else r.2.1
  | .inr _ => r.2.2.2.2

theorem tupleLabel_injective (r : Tuple5 V) (g : EdgeGraph V) (p : goodTuple g r) :
    Function.Injective (tupleLabel r) := by
  rcases r with ⟨u,v,x,y,z⟩
  rcases p with ⟨uv,xy,zx,zy,ux,uy,vx,vy,uz,vz,_⟩
  intro i j hh
  rcases i with (i|i)|i <;> rcases j with (j|j)|j
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals first | rfl | (simp [tupleLabel] at hh; grind)

theorem tupleLabel_distinct (r : Tuple5 V) (j : Function.Injective (tupleLabel r)) :
    r.1≠r.2.1 ∧ r.2.2.1≠r.2.2.2.1 ∧
    r.2.2.2.2≠r.2.2.1 ∧ r.2.2.2.2≠r.2.2.2.1 ∧
    r.1≠r.2.2.1 ∧ r.1≠r.2.2.2.1 ∧
    r.2.1≠r.2.2.1 ∧ r.2.1≠r.2.2.2.1 ∧
    r.1≠r.2.2.2.2 ∧ r.2.1≠r.2.2.2.2 := by
  have e (i l : Five) (h : i≠l) := j.ne h
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [tupleLabel] using e (.inl (.inr 0)) (.inl (.inr 1)) (by decide)
  · simpa [tupleLabel] using e (.inl (.inl 0)) (.inl (.inl 1)) (by decide)
  · simpa [tupleLabel] using e (.inr ()) (.inl (.inl 0)) (by decide)
  · simpa [tupleLabel] using e (.inr ()) (.inl (.inl 1)) (by decide)
  · simpa [tupleLabel] using e (.inl (.inr 0)) (.inl (.inl 0)) (by decide)
  · simpa [tupleLabel] using e (.inl (.inr 0)) (.inl (.inl 1)) (by decide)
  · simpa [tupleLabel] using e (.inl (.inr 1)) (.inl (.inl 0)) (by decide)
  · simpa [tupleLabel] using e (.inl (.inr 1)) (.inl (.inl 1)) (by decide)
  · simpa [tupleLabel] using e (.inl (.inr 0)) (.inr ()) (by decide)
  · simpa [tupleLabel] using e (.inl (.inr 1)) (.inr ()) (by decide)

theorem forbidden_labeled_iff (r : Tuple5 V) (j : Function.Injective (tupleLabel r))
    (g : EdgeGraph V) :
    labeledPattern subEdges ⟨tupleLabel r,j⟩ g ↔ goodTuple g r := by
  rcases r with ⟨u,v,x,y,z⟩
  obtain ⟨uv,xy,zx,zy,ux,uy,vx,vy,uz,vz⟩ := tupleLabel_distinct _ j
  rw [subEdges,page_labeled_iff,diamond_labeled_iff]
  simp [oldLabels,tupleLabel,goodTuple,tupleEdges,forbiddenEdges,Finset.insert_subset_iff,
    hasEdge,Finset.pair_comm,uv,xy,zx,zy,ux,uy,vx,vy,uz,vz,Ne.symm, and_left_comm,
    and_assoc,and_comm]

#print axioms forbidden_labeled_iff
end RobustFolkman.GeometricGap
