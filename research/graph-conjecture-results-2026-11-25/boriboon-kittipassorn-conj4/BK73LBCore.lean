import BK73Core
/-! Computational core for the lower bound m(7,3) ≥ 14: the 13-edge graph FCZnw
(edges 03 05 06 14 15 16 24 25 26 36 45 46 56) has no orientation of diameter ≤ 3. -/
namespace BK73

def m0 : Nat := 1996596

def EPn : List (Nat × Nat) :=
  [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),
   (2,3),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6),(4,5),(4,6),(5,6)]

def mask0 : List Bool := EPn.map (fun p => ab m0 p.1 p.2)

def sel : List Bool → List Bool → List Bool
  | [], _ => []
  | _, [] => []
  | true :: ms, b :: l => b :: sel ms l
  | false :: ms, _ :: l => sel ms l

def expand : List Bool → List Bool → List Bool
  | [], _ => []
  | true :: ms, s => s.headD false :: expand ms s.tail
  | false :: ms, s => false :: expand ms s

/-- some vertex fails to reach some vertex within 3 steps -/
def bad3 (m t : Nat) : Bool :=
  (List.range 7).any (fun u => (List.range 7).any (fun v =>
    !(reach3 ((List.range 7).map (orow m t)) u).testBit v))

def lbp (s : List Bool) : Bool := bad3 m0 (ofBits (expand mask0 s))

/-- BFS closure from 0 for a Bool adjacency on Fin 7 -/
def bfsStep (A : Fin 7 → Fin 7 → Bool) (S : Fin 7 → Bool) : Fin 7 → Bool :=
  fun x => S x || (List.finRange 7).any (fun y => S y && A y x)

def bfsN (A : Fin 7 → Fin 7 → Bool) : Nat → (Fin 7 → Bool)
  | 0 => fun x => x == 0
  | n+1 => bfsStep A (bfsN A n)

def bfs (A : Fin 7 → Fin 7 → Bool) : Fin 7 → Bool := bfsN A 6

def adjDel (a b x y : Fin 7) : Bool :=
  ab m0 x y && !((x == a && y == b) || (x == b && y == a))

end BK73
