import RibbonD3P3Data
import RibbonD3P3Key

namespace RibbonD3P3
open RibbonDumbbell Ribbon5Bridge
abbrev Row := RibbonP3.Row

def atRow (v : Array Row) (i : Nat) : Row :=
  (v[i]?).getD RibbonP3.zeroRow

def rowPoint (q t : Fin 3) (i : Tag) : Row :=
  let D := spec q t
  if i.val < 32 then atRow D.ta i.val
  else if i.val < 64 then atRow D.tb (i.val-32)
  else atRow D.tp (i.val-63)

def TableOK (A : Array Row) (w : Array P) : Prop :=
  (∀ i : Fin 32, RibbonP3.march (atRow A i.val) w[i.val]! = atRow A (i.val+1)) ∧
  ∀ i : Fin 33, RibbonP3.Range (atRow A i.val).i
instance (A : Array Row) (w : Array P) : Decidable (TableOK A w) := by
  unfold TableOK RibbonP3.Range
  infer_instance

def shape (q t : Fin 3) : Prop :=
  let D := spec q t
  atRow D.ta 0 = RibbonP3.zeroRow ∧ atRow D.tp 0 = RibbonP3.zeroRow ∧
  atRow D.tb 0 = atRow D.tp 32 ∧ (atRow D.tp 32).rim = D.bside ∧
  TableOK D.ta D.W.a ∧ TableOK D.tp D.W.p ∧ TableOK D.tb D.W.b
instance (q t : Fin 3) : Decidable (shape q t) := by unfold shape; infer_instance

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem shape_checked (q t : Fin 3) : shape q t := by
  fin_cases q <;> fin_cases t <;> decide +kernel

def atBounds (q t : Fin 3) (i : Tag) : Prop :=
  let r := rowPoint q t i
  (-1 : Int) ≤ r.i ∧ r.i ≤ 1 ∧ (spec q t).yMin ≤ r.j ∧ r.j ≤ (spec q t).yMin+2
instance (q t : Fin 3) (i : Tag) : Decidable (atBounds q t i) := by unfold atBounds; infer_instance

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem bounds_checked (q t : Fin 3) : ∀ i : Tag, atBounds q t i := by
  fin_cases q <;> fin_cases t <;> decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem inverse_checked (q t : Fin 3) :
    ∀ i : Tag, (spec q t).inv[key q t (rowPoint q t i)]! = i.val := by
  fin_cases q <;> fin_cases t <;> decide +kernel

theorem key_injective (q t : Fin 3) : Function.Injective (fun i : Tag => key q t (rowPoint q t i)) := by
  intro i j E
  change key q t (rowPoint q t i) = key q t (rowPoint q t j) at E
  apply Fin.ext
  rw [←inverse_checked q t i,←inverse_checked q t j,E]

#print axioms key_injective
end RibbonD3P3
