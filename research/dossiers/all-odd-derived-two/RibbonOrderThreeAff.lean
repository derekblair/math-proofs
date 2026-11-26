import RibbonOrderThreeLow
import RibbonP11PairPacked

namespace RibbonOrderThree
open RibbonStationaryWord RibbonP11Charts
set_option maxRecDepth 25000
set_option maxHeartbeats 0

def lowPack (s : Bool×ℤ×ℤ×ZMod 3) : Nat :=
  (if s.1 then 3000 else 0)+3*(50*(s.2.1+10).toNat+(s.2.2.1+10).toNat)+s.2.2.2.val

def lowRow (k : W3) : Array Nat :=
  Array.ofFn fun i : Fin 64 => lowPack (lowKey k i)

def digit (p a : Nat) : ZMod p := a
def coeffX (p a : Nat) : ZMod p := if a=1 then 1 else 0
def coeffY (p a : Nat) : ZMod p := if a=1 then 0 else 1

def affPt (p a b : Nat) (k : Count) (i : Fin 64) : Flat (ZMod p) :=
  flatPosition (digit p a) ((digit p a)^(p-2)) (digit p b) ((digit p b)^(p-2))
    (coeffX p a) (coeffY p a) (spec k) i.val

def affPts (p a b : Nat) (k : Count) : List (Flat (ZMod p)) :=
  (spec k).T.scanl
    (flatStep (digit p a) ((digit p a)^(p-2)) (digit p b) ((digit p b)^(p-2))
        (coeffX p a) (coeffY p a))
    (false,1,0)

def affPack (p : Nat) (s : Flat (ZMod p)) : Nat :=
  (if s.1 then p*p else 0) + p*s.2.1.val + s.2.2.val

def affRow (p a b : Nat) (k : Count) : Array Nat :=
  ((affPts p a b k).map (affPack p)).toArray

theorem low_at (k : W3) (i : Fin 64) : (lowRow k)[i.val]! = lowPack (lowKey k i) := by
  rw [getElem!_pos (lowRow k) i.val (by simpa [lowRow] using i.isLt)]
  simp [lowRow]

theorem aff_length (p a b : Nat) (k : Count) : (affPts p a b k).length=65 := by
  simpa [affPts,List.length_scanl] using congrArg Nat.succ (all_valid k).1

theorem aff_at (p a b : Nat) (k : Count) (i : Fin 64) :
    (affRow p a b k)[i.val]! = affPack p (affPt p a b k i) := by
  have l : i.val < (affPts p a b k).length := by rw [aff_length]; omega
  have l' : i.val < (affRow p a b k).size := by simpa [affRow] using l
  have h : (affPts p a b k)[i.val]'l=affPt p a b k i := by
    unfold affPts affPt flatPosition
    exact List.getElem_scanl _
  rw [getElem!_pos (affRow p a b k) i.val l']
  simp only [affRow,List.getElem_toArray,List.getElem_map,h]

theorem both_checked {p a b : Nat} {k : W3}
    (h : RibbonP11Pair.checkRows (lowRow k) (affRow p a b (wid k)) (spec (wid k))=true)
    (i j : Fin 64) (lt : i.val<j.val) (lo : lowKey k i=lowKey k j)
    (hi : affPt p a b (wid k) i=affPt p a b (wid k) j) :
    IsMate (spec (wid k)) i.val j.val := by
  have h' := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  have h'' := List.all_eq_true.mp h' j.val (List.mem_range.mpr j.isLt)
  simpa only [decide_eq_true lt,low_at,aff_at,congrArg lowPack lo,congrArg (affPack p) hi,
    beq_self_eq_true,Bool.true_and,Bool.not_true,Bool.false_or,decide_eq_true_eq] using h''

end RibbonOrderThree
#print axioms RibbonOrderThree.both_checked
