import Std

namespace WowII256

def vertices (n : Nat) : List (Fin n) := List.finRange n
abbrev Adj (n : Nat) := Fin n → Fin n → Bool

def isSimple (n : Nat) (e : Adj n) : Bool :=
  (vertices n).all fun u => !e u u &&
    (vertices n).all fun v => e u v == e v u

def openNbrs (n : Nat) (e : Adj n) (s : List (Fin n)) : List (Fin n) :=
  (vertices n).filter fun v => s.any fun u => e u v

def deg (n : Nat) (e : Adj n) (u : Fin n) : Nat := (openNbrs n e [u]).length

def minDegVertices (n : Nat) (e : Adj n) : List (Fin n) :=
  (vertices n).filter fun u => (vertices n).all fun v => deg n e u <= deg n e v

def maxEdgeNbr (n : Nat) (e : Adj n) : Nat :=
  ((vertices n).flatMap fun u => (vertices n).filterMap fun v =>
    if e u v then some (openNbrs n e [u,v]).length else none).foldl max 0

def totallyDominates (n : Nat) (e : Adj n) (s : List (Fin n)) : Bool :=
  (vertices n).all fun v => s.any fun u => e u v

def edges : List (Nat × Nat) :=
  [(0,1),(1,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),
   (2,9),(2,10),(2,11),(2,12),(2,13),(2,14),
   (3,4),(5,6),(7,8),(9,10),(11,12),(13,14)]

def graph : Adj 15 := fun u v =>
  edges.contains (u.val,v.val) || edges.contains (v.val,u.val)

def dominating : List (Fin 15) := [0,1,2]

-- Each vertex can reach vertex 1 within two graph edges (equality means stay).
def reachesHub (v : Fin 15) : Bool :=
  (vertices 15).any fun a =>
    (v == a || graph v a) && (a == 1 || graph a 1)

set_option maxRecDepth 4096
set_option maxHeartbeats 0

theorem witnessFacts :
    isSimple 15 graph = true ∧
    (vertices 15).all reachesHub = true ∧
    dominating.Nodup ∧ totallyDominates 15 graph dominating = true ∧
    (openNbrs 15 graph (minDegVertices 15 graph)).length = 14 ∧
    maxEdgeNbr 15 graph = 9 := by decide

theorem noTwo :
    (vertices 15).all (fun u => (vertices 15).all fun v =>
      !totallyDominates 15 graph [u,v]) = true := by decide

-- Numeric form: testing a dominating set suffices, because the minimum
-- total-domination cardinality is at most the size of any such set.
theorem strictViolation :
    dominating.length * maxEdgeNbr 15 graph <
      2 * (openNbrs 15 graph (minDegVertices 15 graph)).length := by decide

-- Relational formulation: a finite walk, not a baked-in connectivity predicate.
inductive Walk {n : Nat} (e : Adj n) : Fin n → Fin n → Prop
  | nil (v) : Walk e v v
  | step {u v w} : e u v = true → Walk e v w → Walk e u w

theorem Walk.trans {n} {e : Adj n} {u v w : Fin n}
    (h : Walk e u v) (k : Walk e v w) : Walk e u w := by
  induction h with
  | nil => exact k
  | step h _ ih => exact Walk.step h (ih k)

theorem Walk.reverse {n} {e : Adj n} {u v : Fin n}
    (symm : ∀ a b, e a b = e b a) (h : Walk e u v) : Walk e v u := by
  induction h with
  | nil => exact Walk.nil _
  | @step a b c h _ ih =>
      exact ih.trans (Walk.step ((symm b a).trans h) (Walk.nil a))

theorem graphSymm (a b : Fin 15) : graph a b = graph b a := by
  simp only [graph, Bool.or_comm]

theorem fromHub (v : Fin 15) : Walk graph v 1 := by
  have h := (List.all_eq_true.mp witnessFacts.2.1) v (List.mem_finRange v)
  obtain ⟨a, _, ha⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at ha
  have hstep {x y : Fin 15} (hxy : x = y ∨ graph x y = true) :
      Walk graph x y := by
    rcases hxy with hxy | hxy
    · cases hxy
      exact Walk.nil _
    · exact Walk.step hxy (Walk.nil _)
  exact (hstep ha.1).trans (hstep ha.2)

def Conjecture : Prop :=
  ∀ (n : Nat) (e : Adj n),
    2 ≤ n →
    isSimple n e = true →
    (∀ u v, Walk e u v) →
    ∀ s : List (Fin n), s.Nodup → totallyDominates n e s = true →
      2 * (openNbrs n e (minDegVertices n e)).length ≤ s.length * maxEdgeNbr n e

-- For a simple connected graph with at least two vertices the original
-- denominator is positive. The bound on the minimum total-dominating
-- cardinality implies this bound for every total dominating set.
theorem refutesConjecture : ¬ Conjecture := by
  intro h
  have hconn : ∀ u v, Walk graph u v :=
    fun u v => (fromHub u).trans ((fromHub v).reverse graphSymm)
  exact (Nat.not_le_of_lt strictViolation)
    (h 15 graph (by decide) witnessFacts.1 hconn dominating witnessFacts.2.2.1 witnessFacts.2.2.2.1)

#print axioms refutesConjecture
#print axioms witnessFacts
#print axioms noTwo
#print axioms strictViolation
end WowII256
