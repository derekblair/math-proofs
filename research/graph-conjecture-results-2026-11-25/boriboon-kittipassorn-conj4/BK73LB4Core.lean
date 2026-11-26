import BK73LBCore
import BK73Core4
/-! Computational core for the lower bound m(7,4) ≥ 11: the 10-edge graph F?qvo
(edges 04 05 06 14 16 25 26 35 36 46) has no orientation of diameter ≤ 4. -/
namespace BK73

def m1 : Nat := 746808

def mask1 : List Bool := EPn.map (fun p => ab m1 p.1 p.2)

/-- some vertex fails to reach some vertex within 4 steps -/
def bad4 (m t : Nat) : Bool :=
  (List.range 7).any (fun u => (List.range 7).any (fun v =>
    !(reach4 ((List.range 7).map (orow m t)) u).testBit v))

def lbp4 (s : List Bool) : Bool := bad4 m1 (ofBits (expand mask1 s))

def adjDel1 (a b x y : Fin 7) : Bool :=
  ab m1 x y && !((x == a && y == b) || (x == b && y == a))

end BK73
