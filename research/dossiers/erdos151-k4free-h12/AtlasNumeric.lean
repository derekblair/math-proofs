import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.FinRange
import Lean.Elab.Tactic.Omega

namespace BikovEight

abbrev E := Nat×Nat

def edgeID (i j : Nat) : Nat :=
  let a := min i j
  let b := max i j
  b*(b-1)/2+a

def hasEdge (m i j : Nat) : Bool :=
  if i=j then false else m.testBit (edgeID i j)

def orderedEdges : List E :=
  (List.range 8).flatMap fun j => (List.range j).map fun i => (i,j)

def cutCheck (m s : Nat) : Bool :=
  ((orderedEdges.filter (fun e => hasEdge m e.1 e.2 &&
    (s.testBit e.1 == s.testBit e.2))).length≤1 : Bool)

def permAt (p i : Nat) : Nat := (p >>> (3*i)) &&& 7

def isoCheck (named m p : Nat) : Bool :=
  decide (((List.range 8).map (permAt p)).Nodup) &&
  orderedEdges.all (fun e => hasEdge named e.1 e.2 ==
    hasEdge m (permAt p e.1) (permAt p e.2))

def cycle5Mask : Nat := 613
def cycle7Mask : Nat := 1098277

def attach5 : Array Nat := #[0,1,2,4,8,16,5,9,10,18,20]

def make5 (p q r e : Nat) : Nat :=
  cycle5Mask ||| (p <<< 10) ||| (q <<< 15) ||| (r <<< 21) |||
  ((e &&& 1) <<< 20) ||| ((e &&& 6) <<< 25)

def make7 (p : Nat) : Nat := cycle7Mask ||| (p <<< 21)

def good5 (p q r e : Nat) : Bool :=
  e != 7 && (!e.testBit 0 || p &&& q == 0) &&
  (!e.testBit 1 || p &&& r == 0) && (!e.testBit 2 || q &&& r == 0)

def good7 (p : Nat) : Bool :=
  (List.range 7).all (fun i => !(p.testBit i && p.testBit ((i+1)%7)))

def word5 (h : Nat) : Nat :=
  make5 attach5[h%11]! attach5[(h/11)%11]! attach5[(h/121)%11]! (h/1331)

def valid5 (h : Nat) : Bool :=
  good5 attach5[h%11]! attach5[(h/11)%11]! attach5[(h/121)%11]! (h/1331)

-- Atlas words in MarkedLinkTable row order.
def names : Array Nat := #[126322752, 126323776, 126323904, 89003200, 59184264, 44506248, 59186376]

-- A certificate ≤255 is a cut; otherwise it is 256 + a 3-bit row
-- label + eight 3-bit values of a permutation.
def check (m val : Nat) : Bool :=
  if val<256 then cutCheck m val
  else
    let i := ((val-256) &&& 7)
    decide (i<7) && isoCheck names[i]! m ((val-256) >>> 3)

end BikovEight
