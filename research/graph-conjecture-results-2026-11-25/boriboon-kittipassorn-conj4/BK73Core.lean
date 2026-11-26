import Mathlib.Data.Nat.Bits
/-
  Computational core for: every bridgeless graph on 7 vertices with ≥ 14 edges
  has an orientation of diameter ≤ 3 (refuting Boriboon–Kittipassorn, arXiv:2508.17569,
  Conjecture 4 at (n,d) = (7,3)). All functions here are evaluated by the Lean kernel
  (`decide +kernel`); no native code is used.
-/
namespace BK73

def ofBits : List Bool → Nat
  | [] => 0
  | b :: l => Nat.bit b (ofBits l)

/-- index of the unordered pair {i,j} (i ≠ j) among the 21 pairs of {0,…,6} -/
def pidx (i j : Nat) : Nat :=
  if i < j then i * (13 - i) / 2 + (j - i - 1) else j * (13 - j) / 2 + (i - j - 1)

/-- adjacency bit of the graph with edge code `m` -/
def ab (m i j : Nat) : Bool := (i != j) && m.testBit (pidx i j)

def deg (m i : Nat) : Nat := ((List.range 7).filter (fun j => ab m i j)).length

/-- direction of the pair {u,v} in orientation code `t` (bit 1: smaller → larger) -/
def dir (t u v : Nat) : Bool := if u < v then t.testBit (pidx u v) else !(t.testBit (pidx v u))

/-- out-neighbourhood bitmask of `u` in the orientation of graph `m` given by code `t` -/
def orow (m t u : Nat) : Nat := ofBits ((List.range 7).map (fun j => ab m u j && dir t u j))

def bigOr (os : List Nat) (S : Nat) : Nat :=
  (List.range 7).foldr (fun w acc => if S.testBit w then acc ||| os.getD w 0 else acc) 0

def step (os : List Nat) (S : Nat) : Nat := S ||| bigOr os S

def reach3 (os : List Nat) (u : Nat) : Nat := step os (step os (step os (2 ^ u)))

def goodOs (os : List Nat) : Bool := (List.range 7).all (fun u => reach3 os u == 127)

def good (m t : Nat) : Bool := goodOs ((List.range 7).map (orow m t))

/-- 71 orientation codes (found offline; first-fit order) -/
def TL : List Nat := [1644171,615337,568890,663097,1641209,312755,611125,1673587,1642263,599847,142955,1106603,1584919,398461,664506,1642869,1842875,91502,1334011,575100,544605,403239,1187638,1445671,1445113,79283,145081,546527,1583865,599421,77611,1864182,566647,1335127,288159,1336046,52827,181884,210231,1322605,288238,1064635,1060670,540532,410554,286069,61037,58741,1576797,1587079,333547,1586165,549806,288239,540021,145005,811516,79097,86971,81275,42606,53110,44887,108023,61099,81517,87542,83695,55038,300783,341502]

def sorted (m : Nat) : Bool :=
  deg m 0 ≤ deg m 1 && deg m 1 ≤ deg m 2 && deg m 2 ≤ deg m 3 && deg m 3 ≤ deg m 4 &&
  deg m 4 ≤ deg m 5 && deg m 5 ≤ deg m 6

def chk (L : List Bool) : Bool :=
  if deg (ofBits L) 0 ≤ 1 then true
  else if !(sorted (ofBits L)) then true
  else TL.any (good (ofBits L))

/-- all lists of `n` booleans with at most `z` `false`s, prepended to `acc` -/
def allL (p : List Bool → Bool) (n : Nat) : Nat → List Bool → Bool :=
  Nat.rec (motive := fun _ => Nat → List Bool → Bool)
    (fun _ acc => p acc)
    (fun _ ih z acc => ih z (true :: acc) &&
        Nat.rec (motive := fun _ => Bool) true (fun z' _ => ih z' (false :: acc)) z)
    n

end BK73
