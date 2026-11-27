import GeometricPatternReindex
import GeometricChargeCount

namespace RobustFolkman.GeometricGap
open Finset
variable {V : Type*} [DecidableEq V] [Fintype V]

theorem hasEdge_flip (g : EdgeGraph V) (u v : V) :
    hasEdge g u v ↔ hasEdge g v u := by
  simp only [hasEdge,ne_comm,Finset.pair_comm]

noncomputable def oldLabels {I : Type*} (l : I⊕Unit ↪ V) : I ↪ V :=
  ⟨fun i => l (.inl i),l.injective.comp Sum.inl_injective⟩

theorem page_labeled_iff {I : Type*} [Fintype I] [DecidableEq I]
    (C : I→I→Prop) (a b : I) (l : I⊕Unit ↪ V) (g : EdgeGraph V) :
    labeledPattern (pageEdges C a b) l g ↔
      labeledPattern C (oldLabels l) g ∧ hasEdge g (l (.inl a)) (l (.inr ())) ∧
      hasEdge g (l (.inl b)) (l (.inr ())) := by
  constructor
  · intro q
    exact ⟨fun i j h => q (.inl i) (.inl j) h, q (.inl a) (.inr ()) (Or.inl rfl),
      q (.inl b) (.inr ()) (Or.inr rfl)⟩
  · rintro ⟨q,qa,qb⟩ i j h
    rcases i with i|i <;> rcases j with j|j
    · exact q i j h
    · cases j
      rcases (show i=a ∨ i=b from h) with rfl|rfl
      · exact qa
      · exact qb
    · cases i
      apply (hasEdge_flip g _ _).mpr
      rcases (show j=a ∨ j=b from h) with rfl|rfl
      · exact qa
      · exact qb
    · exact False.elim h

theorem edge_labeled_iff (l : Fin 2 ↪ V) (g : EdgeGraph V) :
    labeledPattern edgeCon l g ↔ hasEdge g (l 0) (l 1) := by
  constructor
  · exact fun h => h 0 1 (by simp [edgeCon,diamondEdges])
  · intro h i j q
    fin_cases i <;> fin_cases j
    · exact False.elim (q rfl)
    · exact h
    · exact (hasEdge_flip g _ _).mp h
    · exact False.elim (q rfl)

theorem diamond_labeled_iff (l : Four ↪ V) (g : EdgeGraph V) :
    labeledPattern diamondEdges l g ↔
      hasEdge g (l (.inl 0)) (l (.inl 1)) ∧
      hasEdge g (l (.inl 0)) (l (.inr 0)) ∧ hasEdge g (l (.inl 0)) (l (.inr 1)) ∧
      hasEdge g (l (.inl 1)) (l (.inr 0)) ∧ hasEdge g (l (.inl 1)) (l (.inr 1)) := by
  constructor
  · intro q
    exact ⟨q (.inl 0) (.inl 1) (by simp [edgeCon,diamondEdges]),q (.inl 0) (.inr 0) trivial,
      q (.inl 0) (.inr 1) trivial,q (.inl 1) (.inr 0) trivial,q (.inl 1) (.inr 1) trivial⟩
  · rintro ⟨uv,ux,uy,vx,vy⟩ i j h
    rcases i with i|i <;> rcases j with j|j
    · exact (edge_labeled_iff ⟨fun i => l (.inl i),l.injective.comp Sum.inl_injective⟩ g).mpr uv i j h
    · fin_cases i <;> fin_cases j
      · exact ux
      · exact uy
      · exact vx
      · exact vy
    · apply (hasEdge_flip g _ _).mpr
      fin_cases i <;> fin_cases j
      · exact ux
      · exact vx
      · exact uy
      · exact vy
    · exact False.elim h

#print axioms diamond_labeled_iff
end RobustFolkman.GeometricGap
