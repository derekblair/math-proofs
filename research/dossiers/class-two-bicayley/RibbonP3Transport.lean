import RibbonP3Collect
import Ribbon5Walk

namespace RibbonP3
open Ribbon5Bridge
variable {G : Type*} [Group G]

def wa (t : Fin 3) : List (Fin 3) := if t=2 then ax else a
def wb (t : Fin 3) : List (Fin 3) := if t=2 then bx else b
def wordAt (t : Fin 3) (i : Fin 64) : List (Fin 3) :=
  if i.val≤32 then (wa t).take i.val else (wb t).take (i.val-32)
def rimRun (w : List (Fin 3)) (s : Bool) : Bool :=
  w.foldl (fun s p => if p=2 then !s else s) s

theorem run_eq_trace (x y : G) (w : List (Fin 3)) (s : Bool) (g : G) :
    run x y (s,g) w = (rimRun w s,g*trace x y s w) := by
  induction w generalizing s g with
  | nil => simp [run,trace,rimRun]
  | cons p w ih =>
    change run x y (action x y (s,g) p) w = _
    cases s <;> fin_cases p <;> simp [action,ih,trace,rimRun,mul_assoc]

set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem row_fold (t : Fin 3) (i : Fin 64) :
    row t i = (wordAt t i).foldl march zeroRow := by
  fin_cases t <;> decide +kernel +revert

theorem rim_fold (t : Fin 3) (i : Fin 64) :
    (row t i).rim = rimRun (wordAt t i) false := by
  fin_cases t <;> decide +kernel +revert

theorem row_safe (t : Fin 3) (i : Fin 64) :
    ∀ r ∈ (wordAt t i).scanl march zeroRow, Range r.i := by
  have test : ((wordAt t i).scanl march zeroRow).all (fun r => decide (-1 ≤ r.i ∧ r.i ≤ 2)) = true := by
    fin_cases t <;> decide +kernel +revert
  intro r hr
  exact show -1 ≤ r.i ∧ r.i ≤ 2 from of_decide_eq_true (List.all_eq_true.mp test r hr)

theorem projected_wordAt {x y c u v : G} (d : Class3 x y c u v) (t : Fin 3) (i : Fin 64) :
    run x y (start G) (wordAt t i) =
       ((row t i).rim,eval x y c u v (row t i)) := by
  have E := eval_fold d (wordAt t i) zeroRow (row_safe t i)
  rw [← row_fold] at E
  rw [start,run_eq_trace,←rim_fold,E]
  simp [eval,zeroRow,HaarClass3Collect.norm]

end RibbonP3
#print axioms RibbonP3.projected_wordAt
