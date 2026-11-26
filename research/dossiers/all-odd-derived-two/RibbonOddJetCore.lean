import RibbonOrderThreeUse
import RibbonOddInterfaces

namespace RibbonOddFinite
open RibbonOrderThree RibbonStationaryWord RibbonP11Charts
set_option maxRecDepth 20000
set_option maxHeartbeats 0

abbrev F (i : Fin 28) := ZMod (inputs i).p
abbrev J (i : Fin 28) := RibbonOdd.J (inputs i).p
abbrev Dir (i : Fin 28) := Fin ((inputs i).p+1)

def direction (i : Fin 28) (d : Dir i) : F i × F i :=
  if d.val=0 then (0,1) else (1,(d.val-1:Nat))

def jet {i : Fin 28} (a da : F i) : J i := ⟨a,da⟩
def jetInv {i : Fin 28} (a da : F i) : J i :=
  jet (a^((inputs i).p-2)) (-(da*(a^((inputs i).p-2))^2))

def coefficients (i : Fin 28) (da db : F i) :
    J i × J i × J i × J i × J i × J i :=
  let z := inputs i
  (jet (digit z.p z.a) da,jetInv (digit z.p z.a) da,
    jet (digit z.p z.b) db,jetInv (digit z.p z.b) db,
    jet (coeffX z.p z.a) 0,jet (coeffY z.p z.a) 0)

def jetPoint (i : Fin 28) (da db : F i) (k : Count) (p : Fin 64) : Flat (J i) :=
  let (a,ai,b,bi,tx,ty) := coefficients i da db
  flatPosition a ai b bi tx ty (spec k) p.val

def jetPoints (i : Fin 28) (da db : F i) (k : Count) : List (Flat (J i)) :=
  let (a,ai,b,bi,tx,ty) := coefficients i da db
  (spec k).T.scanl (flatStep a ai b bi tx ty) (false,1,0)

def jetKey (i : Fin 28) (s : Flat (J i)) : Nat :=
  let p := (inputs i).p
  let a := s.2.1
  let b := s.2.2
  p^4 * (if s.1 then 1 else 0) + p^3*a.fst.val + p^2*a.snd.val + p*b.fst.val+b.snd.val

def jetRow (i : Fin 28) (da db : F i) (k : Count) : Array Nat :=
  ((jetPoints i da db k).map (jetKey i)).toArray

theorem points_length (i : Fin 28) (da db : F i) (k : Count) :
    (jetPoints i da db k).length=65 := by
  simpa [jetPoints,List.length_scanl] using congrArg Nat.succ (all_valid k).1

theorem points_at (i : Fin 28) (da db : F i) (k : Count) (p : Fin 64) :
    (jetPoints i da db k)[p.val]'(by rw [points_length]; omega) = jetPoint i da db k p := by
  unfold jetPoints jetPoint flatPosition
  exact List.getElem_scanl _

theorem jet_at (i : Fin 28) (da db : F i) (k : Count) (p : Fin 64) :
    (jetRow i da db k)[p.val]! = jetKey i (jetPoint i da db k p) := by
  have l : p.val < (jetPoints i da db k).length := by rw [points_length]; omega
  have h : p.val < (jetRow i da db k).size := by simpa [jetRow] using l
  rw [getElem!_pos (jetRow i da db k) p.val h]
  simp only [jetRow,List.getElem_toArray,List.getElem_map,points_at]

theorem jets_sound {i : Fin 28} {da db : F i} {k : Count}
    (h : RibbonP11Pair.checkRows (jetRow i da db k) (jetRow i da db k) (spec k)=true)
    (p q : Fin 64) (lt : p.val<q.val) (e : jetPoint i da db k p=jetPoint i da db k q) :
    IsMate (spec k) p.val q.val := by
  have h' := List.all_eq_true.mp h p.val (List.mem_range.mpr p.isLt)
  have h'' := List.all_eq_true.mp h' q.val (List.mem_range.mpr q.isLt)
  simpa only [decide_eq_true lt,jet_at,congrArg (jetKey i) e,
    beq_self_eq_true,Bool.true_and,Bool.not_true,Bool.false_or,decide_eq_true_eq] using h''

end RibbonOddFinite
#print axioms RibbonOddFinite.jets_sound
