import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod

namespace RobustFolkman.GeometricPatterns
open Finset

def e : Finset (Nat × Nat) := {(0,1)}
def t : Finset (Nat × Nat) := {(0,1),(0,2),(1,2)}
def d : Finset (Nat × Nat) := {(2,3),(0,2),(0,3),(1,2),(1,3)}
def h : Finset (Nat × Nat) := insert (0,4) (insert (1,4) d)
def j : Finset (Nat × Nat) := insert (0,5) (insert (4,5) h)

def triangles (N : Nat) (F : Finset (Nat × Nat)) : Finset (Nat × Nat × Nat) :=
  ((range N).product ((range N).product (range N))).filter fun (a,b,c) =>
    a<b ∧ b<c ∧ (a,b)∈F ∧ (a,c)∈F ∧ (b,c)∈F

theorem counts :
    e.card=1 ∧ (triangles 2 e).card=0 ∧
    t.card=3 ∧ (triangles 3 t).card=1 ∧
    d.card=5 ∧ (triangles 4 d).card=2 ∧
    h.card=7 ∧ (triangles 5 h).card=2 ∧
    j.card=9 ∧ (triangles 6 j).card=3 := by decide

theorem shared_marked_edge : (0,4)∈h ∧ h⊆j ∧ j\h={(0,5),(4,5)} := by decide

#print axioms counts
#print axioms shared_marked_edge
end RobustFolkman.GeometricPatterns
