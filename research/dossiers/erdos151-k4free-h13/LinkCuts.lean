import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Range

namespace BikovLocal
abbrev E := Nat × Nat

def c5 : List E := [(0,1),(1,2),(2,3),(3,4),(0,4)]
def c7 : List E := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(0,6)]
def extra : List E := [(0,5),(0,6),(1,5),(1,6),(2,5),(2,6),(3,5),(3,6),(4,5),(4,6),(5,6)]

def edges (mask : Nat) : List E :=
  c5 ++ (extra.zipIdx.filter (fun (_,i)=>mask.testBit i)).map Prod.fst

def tris : List (Nat×Nat×Nat) :=
  (List.range 7).flatMap fun i => (List.range 7).flatMap fun j =>
    (List.range 7).filterMap fun k => if i<j ∧ j<k then some (i,j,k) else none

def triFree (es : List E) : Bool :=
  tris.all fun (i,j,k) => !(es.contains (i,j) && es.contains (i,k) && es.contains (j,k))

def defect (es : List E) (s : Nat) : List E :=
  es.filter (fun (i,j) => s.testBit i == s.testBit j)

def rows : List (Nat×Nat) :=
  [(51,5),(99,13),(147,13),(195,9),(198,11),(201,11),(204,10),(306,21),(396,26),
   (561,21),(588,26),(780,18),(792,22),(804,22),(816,20),(1126,37),(1177,42),
   (1318,37),(1414,41),(1426,41),(1432,42),(1561,50),(1609,50),(1633,52),(1636,52)]

def check (m : Nat) : Bool :=
  !triFree (edges m) || rows.any (fun (u,_) => m &&& u == m)

theorem rows_cut : ∀ p∈rows, (defect (edges p.1) p.2).length≤1 := by decide +kernel

theorem cycle7_cut : (defect c7 21).length≤1 := by decide +kernel

end BikovLocal
