import Mathproofs.Girth5Floor3v

/-! Regression witnesses from the October 2026 hostile review. The old predicate
accepted each of these invalid moves; the corrected local conditions reject them.
The identity sanity checks ensure the corrected predicate is inhabited. -/

namespace Girth5Floor3v.Regression

def empty4 : Girth5Graph (Fin 4) where
  adj := fun _ _ => False
  decAdj := inferInstance
  symm := by simp
  irrefl := by simp
  noTri := by simp
  noC4 := by simp

def path3 : Girth5Graph (Fin 3) where
  adj := fun x y => x.val + 1 = y.val ∨ y.val + 1 = x.val
  decAdj := inferInstance
  symm := by decide
  irrefl := by decide
  noTri := by decide
  noC4 := by decide

def oldEdge5 : Girth5Graph (Fin 5) where
  adj := fun x y => (x = 3 ∧ y = 4) ∨ (x = 4 ∧ y = 3)
  decAdj := inferInstance
  symm := by decide
  irrefl := by decide
  noTri := by decide
  noC4 := by
    intro a b c d hab hbc hcd hda
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all

/-- Cross-edge guards also use the candidate internal edge rather than the old graph. -/
theorem cross_edge_move_rejected :
    ¬ IsFeasible oldEdge5 0 1 2 {3} {4} ∅ {(0, 1)} := by
  intro h
  exact h.crossAB (by simp) 3 (by simp) 4 (by simp) (by decide)

/-- A newly added internal edge cannot share an attachment at its endpoints. -/
theorem triangle_move_rejected :
    ¬ IsFeasible empty4 0 1 2 {3} {3} ∅ {(0, 1)} := by
  intro h
  have he := h.disjointAB (by simp)
  simp at he

/-- An attachment must lie outside the removed triple. -/
theorem loop_move_rejected :
    ¬ IsFeasible empty4 0 1 2 {0} ∅ ∅ ∅ := by
  intro h
  have hw := h.attachA (by simp : (0 : Fin 4) ∈ ({0} : Finset (Fin 4)))
  simp [W] at hw

/-- Endpoints of a two-edge internal path cannot share an attachment. -/
theorem four_cycle_move_rejected :
    ¬ IsFeasible empty4 0 1 2 {3} ∅ {3} {(0, 1), (1, 2)} := by
  intro h
  have he := h.pathAC (by simp) (by simp)
  simp at he

/-- The spurious score-five move on an extremal three-vertex path is excluded. -/
theorem path_bad_move_rejected :
    ¬ IsFeasible path3 0 1 2 {0, 2} ∅ {0} {(0, 1), (1, 2)} := by
  intro h
  have hw := h.attachA (by simp : (0 : Fin 3) ∈ ({0, 2} : Finset (Fin 3)))
  simp [W] at hw

theorem empty_identity_feasible :
    IsFeasible empty4 0 1 2 (A empty4 0 1 2) (B empty4 0 1 2)
      (C empty4 0 1 2) (P empty4 0 1 2) :=
  identity_feasible empty4 0 1 2 (by decide) (by decide) (by decide)

theorem path_identity_feasible :
    IsFeasible path3 0 1 2 (A path3 0 1 2) (B path3 0 1 2)
      (C path3 0 1 2) (P path3 0 1 2) :=
  identity_feasible path3 0 1 2 (by decide) (by decide) (by decide)

end Girth5Floor3v.Regression
