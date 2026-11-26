import HaarCycle
import Mathlib.Tactic

namespace HaarClass3Table

abbrev Coord := ℤ × ℤ × ℤ × ℤ × ℤ

def table : Fin 32 → Coord := fun i => (#[(0, 0, 0, 0, 0), (0, 0, 0, 0, 0), (-1, 0, 0, 0, 0), (-1, 0, 0, 0, 0),
  (-1, -1, 1, -1, -1), (0, -1, 1, 0, -1), (0, -1, 1, 0, -1), (0, 0, 1, 0, 0),
  (-1, 0, 1, -1, 0), (-1, 1, 0, 0, 1), (-1, 1, 0, 0, 1), (0, 1, 0, 0, 1),
  (0, 0, 0, 0, 1), (0, 0, 0, 0, 1), (-1, 0, 0, 0, 1), (-1, 0, 0, 0, 1),
  (-2, 0, 0, 0, 1), (-2, 1, -2, 3, 1), (-2, 1, -2, 3, 1), (-1, 1, -2, 1, 1),
  (-1, 0, -1, 0, 2), (0, 0, -1, -1, 2), (0, 0, -1, -1, 2), (0, 1, -1, -1, 1),
  (-1, 1, -1, 0, 1), (-1, 2, -2, 1, 0), (-2, 2, -2, 3, 0), (-2, 2, -2, 3, 0),
  (-2, 1, 0, 0, 0), (-1, 1, 0, 0, 0), (-1, 1, 0, 0, 0), (0, 1, 0, 0, 0)] : Array Coord)[i.val]!

def dx (p : Coord) : Coord :=
  (p.1+1,p.2.1,p.2.2.1,p.2.2.2.1+p.2.2.1,p.2.2.2.2)

def dy (p : Coord) : Coord :=
  (p.1,p.2.1+1,p.2.2.1+p.1,p.2.2.2.1+p.1*(p.1-1)/2,p.2.2.2.2+p.2.2.1)

def edge (p q : Coord) : Prop := q=p ∨ q=dx p ∨ q=dy p
instance (p q : Coord) : Decidable (edge p q) := by unfold edge; infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 600000 in
theorem step (i : Fin 32) :
    if HaarCycle.side i then edge (table (i+1)) (table i) else edge (table i) (table (i+1)) := by
  revert i
  decide

def modest (d : ℤ) : Prop := |d|=1 ∨ |d|=2
instance (d : ℤ) : Decidable (modest d) := by unfold modest; infer_instance

set_option maxRecDepth 15000 in
set_option maxHeartbeats 2000000 in
theorem split (i j : Fin 32) :
    i=j ∨ HaarCycle.side i ≠ HaarCycle.side j ∨
    modest ((table i).1-(table j).1) ∨ modest ((table i).2.1-(table j).2.1) ∨
    ((table i).1=(table j).1 ∧ (table i).2.1=(table j).2.1 ∧
       modest ((table i).2.2.1-(table j).2.2.1)) ∨
    ((table i).1=(table j).1 ∧ (table i).2.1=(table j).2.1 ∧
       (table i).2.2.1=(table j).2.2.1 ∧ (table i).2.2.2.1=(table j).2.2.2.1 ∧
       |(table i).2.2.2.2-(table j).2.2.2.2|=1) := by
  revert i j
  decide

end HaarClass3Table

#print axioms HaarClass3Table.step
#print axioms HaarClass3Table.split
