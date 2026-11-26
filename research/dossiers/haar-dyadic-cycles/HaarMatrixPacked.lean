import Mathlib.Data.Nat.Basic

namespace HaarMatrixPacked

def zero : Array ℕ := Array.replicate 15 0

def xp (x : Array ℕ) : Array ℕ := #[
  (2+x[0]!)%17,
  (0+x[1]!+1*x[0]!)%17,
  (0+x[2]!+7*x[1]!)%17,
  (0+x[3]!+1*x[2]!)%17,
  (0+x[4]!+15*x[3]!)%17,
  (1+x[5]!)%17,
  (0+x[6]!+7*x[5]!)%17,
  (0+x[7]!+1*x[6]!)%17,
  (0+x[8]!+15*x[7]!)%17,
  (7+x[9]!)%17,
  (0+x[10]!+1*x[9]!)%17,
  (0+x[11]!+15*x[10]!)%17,
  (1+x[12]!)%17,
  (0+x[13]!+15*x[12]!)%17,
  (15+x[14]!)%17
]
def yp (x : Array ℕ) : Array ℕ := #[
  (1+x[0]!)%17,
  (0+x[1]!+5*x[0]!)%17,
  (0+x[2]!+15*x[1]!)%17,
  (0+x[3]!+9*x[2]!)%17,
  (0+x[4]!+15*x[3]!)%17,
  (5+x[5]!)%17,
  (0+x[6]!+15*x[5]!)%17,
  (0+x[7]!+9*x[6]!)%17,
  (0+x[8]!+15*x[7]!)%17,
  (15+x[9]!)%17,
  (0+x[10]!+9*x[9]!)%17,
  (0+x[11]!+15*x[10]!)%17,
  (9+x[12]!)%17,
  (0+x[13]!+15*x[12]!)%17,
  (15+x[14]!)%17
]
def xn (x : Array ℕ) : Array ℕ := #[
  (15+x[0]!)%17,
  (2+x[1]!+16*x[0]!)%17,
  (3+x[2]!+7*x[0]!+10*x[1]!)%17,
  (14+x[3]!+10*x[0]!+7*x[1]!+16*x[2]!)%17,
  (11+x[4]!+3*x[0]!+14*x[1]!+15*x[2]!+2*x[3]!)%17,
  (16+x[5]!)%17,
  (7+x[6]!+10*x[5]!)%17,
  (10+x[7]!+7*x[5]!+16*x[6]!)%17,
  (3+x[8]!+14*x[5]!+15*x[6]!+2*x[7]!)%17,
  (10+x[9]!)%17,
  (7+x[10]!+16*x[9]!)%17,
  (14+x[11]!+15*x[9]!+2*x[10]!)%17,
  (16+x[12]!)%17,
  (15+x[13]!+2*x[12]!)%17,
  (2+x[14]!)%17
]
def yn (x : Array ℕ) : Array ℕ := #[
  (16+x[0]!)%17,
  (5+x[1]!+12*x[0]!)%17,
  (10+x[2]!+7*x[0]!+2*x[1]!)%17,
  (12+x[3]!+5*x[0]!+16*x[1]!+8*x[2]!)%17,
  (7+x[4]!+10*x[0]!+15*x[1]!+16*x[2]!+2*x[3]!)%17,
  (12+x[5]!)%17,
  (7+x[6]!+2*x[5]!)%17,
  (5+x[7]!+16*x[5]!+8*x[6]!)%17,
  (10+x[8]!+15*x[5]!+16*x[6]!+2*x[7]!)%17,
  (2+x[9]!)%17,
  (16+x[10]!+8*x[9]!)%17,
  (15+x[11]!+16*x[9]!+2*x[10]!)%17,
  (8+x[12]!)%17,
  (16+x[13]!+2*x[12]!)%17,
  (2+x[14]!)%17
]

def move (pos : Bool) (port : ℕ) (a : Array ℕ) : Array ℕ :=
  if port=0 then a else
  if port=1 then (if pos then xp a else xn a) else (if pos then yp a else yn a)

def key (a : Array ℕ) : ℕ := a.toList.foldl (fun n b => 17*n+b) 0

def words (a : Array ℕ) (pos : Bool) (last : ℕ) : ℕ → List ℕ
  | 0 => [key a]
  | n+1 => [0,1,2].flatMap fun j => if j=last then [] else words (move pos j a) (!pos) j n

def strict : List ℕ → Bool
  | [] => true
  | [_] => true
  | a::b::l => (a < b) && strict (b::l)

def census (n : ℕ) : ℕ × Bool :=
  let keys := words zero true 3 n
  (keys.length, strict (keys.mergeSort (·≤·)))

/-- info: (98304, true) -/
#guard_msgs in
#eval census 16

end HaarMatrixPacked
