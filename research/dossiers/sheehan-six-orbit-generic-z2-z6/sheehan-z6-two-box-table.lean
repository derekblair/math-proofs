import Lean
namespace TwoBoxes
def pos (x : Nat) : List Nat → Nat
 | [] => 0
 | h::t => if h == x then 0 else 1 + pos x t
def entry (L : List Nat) (x : Nat) := L[x]?.getD 0
def rot (L : List Nat) (rev : Bool) (x : Nat) :=
 entry L ((pos x L + if rev then 7 else 1) % 8)
def doubled (L : List Nat) := L.flatMap (fun x => [x,x+4])
def aCap (blockA : Bool) (x : Nat) :=
 entry (if blockA then [7,2,1,4,3,6,5,0] else [7,4,5,6,1,2,3,0]) x
def bCap (blockA : Bool) (x : Nat) :=
 entry (if blockA then [7,6,4,5,2,3,1,0] else [7,2,1,4,3,6,5,0]) x
def check (blockA : Bool) (O R : List Nat) :=
 let A := doubled O
 let B := doubled R
 let v := O == R
 let next := fun x => rot A false (rot B (!v) (bCap blockA (rot B v (rot A true (aCap blockA x)))))
 let a := next 0
 let b := next a
 let c := next b
 a != 0 && b != 0 && c != 0 && a != b && a != c && b != c && next c == 0
def chart (f : Bool) (O R : List Nat) : Prop := check f O R = true
theorem chartA :
 chart true [0,1,2,3] [0,1,2,3] ∧
 chart true [0,1,2,3] [0,3,2,1] ∧
 chart true [0,3,2,1] [0,1,2,3] ∧
 chart true [0,3,2,1] [0,3,2,1] := ⟨rfl, rfl, rfl, rfl⟩
theorem chartB :
 chart false [0,2,1,3] [0,2,1,3] ∧
 chart false [0,2,1,3] [0,3,1,2] ∧
 chart false [0,3,1,2] [0,2,1,3] ∧
 chart false [0,3,1,2] [0,3,1,2] := ⟨rfl, rfl, rfl, rfl⟩
#print axioms chartA
#print axioms chartB
end TwoBoxes
