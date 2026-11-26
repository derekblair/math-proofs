import Ribbon6P3Key
import Ribbon6P3Local
import RibbonP3Transport
namespace Ribbon6
open RibbonP3 Ribbon5Bridge HaarClass3Collect

variable {G H : Type*} [Group G] [Group H]
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private theorem prow_def (i : Fin 64) :
    prow i=(wc.toList.take i.val).foldl march zeroRow := by decide +kernel +revert

private theorem row_rim (i : Fin 64) :
    (prow i).rim = rimRun (wc.toList.take i.val) false := by decide +kernel +revert

private theorem safe (i : Fin 64) :
    ∀ r' ∈ (wc.toList.take i.val).scanl march zeroRow, Range r'.i := by
  have test : (wc.toList.scanl march zeroRow).all (fun r => decide (-1≤r.i ∧ r.i≤2)) = true := by
    decide +kernel
  intro r hr
  have h : r ∈ wc.toList.scanl march zeroRow := by
    rw [← List.take_scanl] at hr
    exact List.mem_of_mem_take hr
  exact show -1 ≤ r.i ∧ r.i ≤ 2 from of_decide_eq_true (List.all_eq_true.mp test r h)

theorem eval_prow (f : G →* H) (x y : G) (c u v : H)
    (cl : Class3 (f x) (f y) c u v) (i : Fin 64) :
    ((pathAt x y wc i.val).1,f (pathAt x y wc i.val).2) =
      ((prow i).rim,eval (f x) (f y) c u v (prow i)) := by
  have H : (fun s : Bool×G => (s.1,f s.2)) (pathAt x y wc i.val) =
      run (f x) (f y) (start H) (wc.toList.take i.val) := by
    rw [pathAt,mapped_run]
    simp only [start,map_one]
  rw [show ((pathAt x y wc i.val).1,f (pathAt x y wc i.val).2) =
    (fun s : Bool×G => (s.1,f s.2)) (pathAt x y wc i.val) from rfl,H]
  have E := eval_fold cl (wc.toList.take i.val) zeroRow (safe i)
  rw [← prow_def] at E
  rw [start,run_eq_trace,←row_rim,E]
  simp [eval,zeroRow,HaarClass3Collect.norm]

end Ribbon6
#print axioms Ribbon6.eval_prow
