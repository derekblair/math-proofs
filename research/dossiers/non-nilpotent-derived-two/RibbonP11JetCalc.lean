import RibbonP11PairPacked
import Mathlib.Algebra.TrivSqZeroExt.Basic
namespace RibbonP11JetCalc
open RibbonP11Pair RibbonP11Charts RibbonStationaryWord
abbrev J := TrivSqZeroExt F F
set_option maxRecDepth 20000
set_option maxHeartbeats 0

def jet (a da : F) : J := ⟨a,da⟩
def jetInv (a da : F) : J := jet (a^9) (-(da*(a^9)^2))

def coefficients (i : Fin 16) (da db : F) :
    J×J×J×J×J×J :=
  let z := bad i
  (jet z.1 da,jetInv z.1 da,jet z.2 db,jetInv z.2 db,
    jet (if z.1=1 then 1 else 0) 0,jet (if z.1=1 then 0 else 1) 0)

def jetPoint (i : Fin 16) (da db : F) (k : Count) (p : Fin 64) : Flat J :=
  let (a,ai,b,bi,tx,ty) := coefficients i da db
  flatPosition a ai b bi tx ty (spec k) p.val

def jetPoints (i : Fin 16) (da db : F) (k : Count) : List (Flat J) :=
  let (a,ai,b,bi,tx,ty) := coefficients i da db
  (spec k).T.scanl (flatStep a ai b bi tx ty) (false,1,0)

def jetKey (s : Flat J) : Nat :=
  let a := s.2.1
  let b := s.2.2
  14641 * (if s.1 then 1 else 0) + 1331*a.fst.val + 121*a.snd.val + 11*b.fst.val+b.snd.val

def jetRow (i : Fin 16) (da db : F) (k : Count) : Array Nat :=
  ((jetPoints i da db k).map jetKey).toArray

theorem points_length (i : Fin 16) (da db : F) (k : Count) :
    (jetPoints i da db k).length=65 := by
  simpa [jetPoints,List.length_scanl] using congrArg Nat.succ (all_valid k).1

theorem points_at (i : Fin 16) (da db : F) (k : Count) (p : Fin 64) :
    (jetPoints i da db k)[p.val]'(by rw [points_length]; omega) = jetPoint i da db k p := by
  unfold jetPoints jetPoint flatPosition
  exact List.getElem_scanl _

theorem row_at (i : Fin 16) (da db : F) (k : Count) (p : Fin 64) :
    (jetRow i da db k)[p.val]! = jetKey (jetPoint i da db k p) := by
  have l : p.val < (jetPoints i da db k).length := by rw [points_length]; omega
  have h : p.val < (jetRow i da db k).size := by simpa [jetRow] using l
  rw [getElem!_pos (jetRow i da db k) p.val h]
  simp only [jetRow, List.getElem_toArray,List.getElem_map,points_at]

theorem row_sound {i : Fin 16} {da db : F} {k : Count}
    (h : checkRows (jetRow i da db k) (jetRow i da db k) (spec k) = true)
    (p q : Fin 64) (lt : p.val<q.val) (e : jetPoint i da db k p=jetPoint i da db k q) :
    IsMate (spec k) p.val q.val := by
  have h' := List.all_eq_true.mp h p.val (List.mem_range.mpr p.isLt)
  have h'' := List.all_eq_true.mp h' q.val (List.mem_range.mpr q.isLt)
  simpa only [decide_eq_true lt,row_at,congrArg jetKey e,
    beq_self_eq_true,Bool.true_and,Bool.not_true,Bool.false_or,decide_eq_true_eq] using h''

end RibbonP11JetCalc
#print axioms RibbonP11JetCalc.row_sound
