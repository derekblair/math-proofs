import RibbonP11Charts
import RibbonD3Interfaces
import RibbonD3FieldCharts
import RibbonD3RowSort

namespace RibbonD3Finite
open Ribbon5Bridge RibbonP11Charts RibbonStationaryChart RibbonD3Field
abbrev Digits := Nat × Nat
abbrev State := Bool × Digits × Digits
abbrev Jet (p : Nat) := RibbonOdd.J p

def add (p : Nat) (x y : Digits) : Digits :=
  ((x.1+y.1)%p,(x.2+y.2)%p)

def mul (p : Nat) (x y : Digits) : Digits :=
  (x.1*y.1%p,(x.1*y.2+x.2*y.1)%p)

def neg (p : Nat) (x : Digits) : Digits := ((p-x.1)%p,(p-x.2)%p)

def digits {p : Nat} (x : Jet p) : Digits := (x.fst.val,x.snd.val)

theorem digits_add {p : Nat} [NeZero p] (x y : Jet p) :
    digits (x+y)=add p (digits x) (digits y) := by
  exact Prod.ext (ZMod.val_add _ _) (ZMod.val_add _ _)

theorem digits_mul {p : Nat} [NeZero p] (x y : Jet p) :
    digits (x*y)=mul p (digits x) (digits y) := by
  fapply Prod.ext
  · exact ZMod.val_mul _ _
  · change (x.fst*y.snd+x.snd*y.fst).val = (x.fst.val*y.snd.val+x.snd.val*y.fst.val)%p
    rw [ZMod.val_add,ZMod.val_mul,ZMod.val_mul]; exact (Nat.add_mod _ _ _).symm

theorem digits_neg {p : Nat} [NeZero p] (x : Jet p) :
    digits (-x)=neg p (digits x) := by
  exact Prod.ext (ZMod.neg_val' _) (ZMod.neg_val' _)

def flatten {p : Nat} (s : Flat (Jet p)) : State :=
  (s.1,digits s.2.1,digits s.2.2)

def step (p : Nat) (a A b B tx ty : Digits) (s : State) (t : P) : State :=
  let (side,m,z) := s
  if t=2 then (!side,m,z) else
    let (q,Q,u) := if side then (b,B,ty) else (a,A,tx)
    if t=0 then (side,mul p m q,add p z (mul p m u)) else
      let r := mul p m Q
      (side,r,add p z (neg p (mul p r u)))

theorem step_sound {p : Nat} [NeZero p]
    (a A b B tx ty : Jet p) (s : Flat (Jet p)) (t : P) :
    flatten (flatStep a A b B tx ty s t) =
      step p (digits a) (digits A) (digits b) (digits B) (digits tx) (digits ty) (flatten s) t := by
  rcases s with ⟨r,m,z⟩
  cases r <;> fin_cases t <;>
    simp [flatten,flatStep,step,sub_eq_add_neg,digits_add,digits_mul,digits_neg]

theorem fold_sound {p : Nat} [NeZero p]
    (a A b B tx ty : Jet p) (w : List P) (s : Flat (Jet p)) :
    flatten (w.foldl (flatStep a A b B tx ty) s) =
      w.foldl (step p (digits a) (digits A) (digits b) (digits B) (digits tx) (digits ty)) (flatten s) := by
  induction w generalizing s with
  | nil => rfl
  | cons t w ih => simp only [List.foldl_cons,ih,step_sound]

def key (p : Nat) (s : State) : Nat :=
  p^4*(if s.1 then 1 else 0) + p^3*s.2.1.1+p^2*s.2.1.2+p*s.2.2.1+s.2.2.2

structure Params where
  p : Nat
  a : Digits
  A : Digits
  b : Digits
  B : Digits
  pivot : Bool
  deriving DecidableEq

def Params.next (v : Params) : State → P → State :=
  step v.p v.a v.A v.b v.B (if v.pivot then (0,0) else (1,0))
    (if v.pivot then (1,0) else (0,0))

def row (v : Params) (k : Count) : Array Nat :=
  (((chart k).ports.scanl v.next ((chart k).start,(1,0),(0,0))).map (key v.p)).toArray

theorem row_at (v : Params) (k : Count) (i : Fin 128) :
    (row v k)[i.val]! = key v.p (((chart k).ports.take i.val).foldl
      v.next ((chart k).start,(1,0),(0,0))) := by
  have sz : i.val < (row v k).size := by
    have L := (charts_shape k).1
    simpa [row,List.length_scanl,L] using Nat.lt_succ_of_lt i.isLt
  rw [getElem!_pos (row v k) i.val sz]
  simp only [row,List.getElem_toArray,List.getElem_map,List.getElem_scanl]

end RibbonD3Finite
