import Std
namespace Erdos151MarkedLinkTable
def edges (i : Fin 7) : List (Fin 8 × Fin 8) :=
  match i.val with
| 0 => [(0,4),(0,6),(1,5),(1,6),(2,6),(2,7),(3,6),(3,7),(4,7),(5,7)]
| 1 => [(0,4),(0,5),(0,6),(1,5),(1,6),(2,6),(2,7),(3,6),(3,7),(4,7),(5,7)]
| 2 => [(0,4),(0,5),(0,6),(1,4),(1,5),(1,6),(2,6),(2,7),(3,6),(3,7),(4,7),(5,7)]
| 3 => [(0,4),(0,5),(1,4),(1,7),(2,5),(2,6),(3,6),(3,7),(4,6),(5,7)]
| 4 => [(0,3),(0,5),(1,4),(1,6),(2,5),(2,6),(2,7),(3,6),(3,7),(4,7)]
| 5 => [(0,3),(0,5),(0,7),(1,4),(1,5),(1,6),(2,5),(2,6),(2,7),(3,6),(4,7)]
| 6 => [(0,3),(0,4),(0,5),(1,4),(1,5),(1,6),(2,5),(2,6),(2,7),(3,6),(3,7),(4,7)]
  | _ => []
def deg (i : Fin 7) (v : Fin 8) : Nat :=
  ((edges i).filter (fun e => e.1 == v || e.2 == v)).length
def adj (i : Fin 7) (v w : Fin 8) : Bool :=
  (edges i).contains (v,w) || (edges i).contains (w,v)
def high (i : Fin 7) : Nat :=
  ((List.finRange 8).filter (fun v => 4 ≤ deg i v)).length
theorem minMax : ∀ i : Fin 7, ∀ v : Fin 8, 2≤deg i v ∧ deg i v≤4 := by decide
theorem highCount : ∀ i : Fin 7, high i=0 ∨ high i=2 := by decide
theorem highIndependent : ∀ i : Fin 7, ∀ u v : Fin 8,
    adj i u v=true → 4≤deg i u → 4≤deg i v → False := by decide
theorem elevenLowIndependent : ∀ i : Fin 7, (edges i).length=11 → high i=0 →
    ∀ u v : Fin 8, adj i u v=true → deg i u=2 → deg i v=2 → False := by decide
def low (i : Fin 7) : Nat := ((List.finRange 8).filter (fun v => deg i v = 2)).length
theorem highMate : ∀ i : Fin 7, ∀ x : Fin 8, 4≤deg i x →
    ∃ y : Fin 8, y≠x ∧ 4≤deg i y := by decide
theorem edges_le : ∀ i : Fin 7, (edges i).length≤12 := by decide
theorem low_deficit : ∀ i : Fin 7, high i=0 →
    low i=2*(12-(edges i).length) := by decide
theorem no_high_low_def : ∀ i : Fin 7,
    (∀ v : Fin 8, deg i v≤3) → high i=0 := by decide
theorem twoLow : ∀ i : Fin 7, (edges i).length=11 → high i=0 →
    ∃ x y : Fin 8, x≠y ∧ deg i x=2 ∧ deg i y=2 := by decide
#print axioms highMate
#print axioms low_deficit
#print axioms twoLow
#print axioms minMax
#print axioms highCount
#print axioms highIndependent
#print axioms elevenLowIndependent
end Erdos151MarkedLinkTable
