import Std
namespace WowII255

def vertices (n : Nat) : List (Fin n) := List.finRange n
abbrev Adj (n : Nat) := Fin n → Fin n → Bool

def isSimple (n : Nat) (e : Adj n) : Bool :=
  (vertices n).all fun u => !e u u &&
    (vertices n).all fun v => e u v == e v u

def openNbrs (n : Nat) (e : Adj n) (s : List (Fin n)) : List (Fin n) :=
  (vertices n).filter fun v => s.any fun u => e u v

def maxEdgeNbr (n : Nat) (e : Adj n) : Nat :=
  ((vertices n).flatMap fun u => (vertices n).filterMap fun v =>
    if e u v then some (openNbrs n e [u,v]).length else none).foldl max 0

def totallyDominates (n : Nat) (e : Adj n) (s : List (Fin n)) : Bool :=
  (vertices n).all fun v => s.any fun u => e u v

def leftWing (i : Nat) : Bool := 3 ≤ i && i < 7
def rightWing (i : Nat) : Bool := 7 ≤ i && i < 11

def oriented (i j : Nat) : Bool :=
  (i == 0 && j == 1) || (i == 1 && j == 2) ||
  (i == 0 && leftWing j) || (i == 2 && rightWing j) ||
  (leftWing i && leftWing j && i != j) ||
  (leftWing i && rightWing j && i-3 == j-7)

def graph : Adj 11 := fun u v => oriented u.val v.val || oriented v.val u.val

def dominating : List (Fin 11) := [0,1,2]

def stepB {n} (e : Adj n) (x y : Fin n) : Bool := x == y || e x y

def withinTwo {n} (e : Adj n) (u v : Fin n) : Bool :=
  (vertices n).any fun w => stepB e u w && stepB e w v

set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem simple : isSimple 11 graph = true := by decide
theorem allTwo :
    (vertices 11).all (fun u => (vertices 11).all (withinTwo graph u)) = true := by decide
theorem noneOne :
    (vertices 11).all (fun u => (vertices 11).any fun v => !stepB graph u v) = true := by decide
theorem domination :
    dominating.Nodup ∧ totallyDominates 11 graph dominating = true := by decide
theorem edgeMaximum : maxEdgeNbr 11 graph = 7 := by decide
theorem strictViolation : dominating.length * maxEdgeNbr 11 graph < 2 * (vertices 11).length := by decide

-- A walk of length at most k, allowing a repeated vertex as a zero-cost wait.
def Within {n} (e : Adj n) : Nat → Fin n → Fin n → Prop
  | 0, u, v => u = v
  | k+1, u, v => ∃ w, (u = w ∨ e u w = true) ∧ Within e k w v

def EccLE {n} (e : Adj n) (u : Fin n) (k : Nat) : Prop :=
  ∀ v, Within e k u v

-- Being no farther out than any vertex, at every possible distance threshold,
-- is equivalent to realizing the minimum eccentricity in a connected graph.
def Center {n} (e : Adj n) (u : Fin n) : Prop :=
  ∀ w k, EccLE e w k → EccLE e u k

theorem Within.raise {n} {e : Adj n} {k u v}
    (h : Within e k u v) : Within e (k+1) u v :=
  ⟨u, Or.inl rfl, h⟩

theorem stepB_iff {n} {e : Adj n} {u v} :
    stepB e u v = true ↔ u = v ∨ e u v = true := by
  simp [stepB, Bool.or_eq_true, beq_iff_eq]

theorem allEccTwo (u : Fin 11) : EccLE graph u 2 := by
  intro v
  have r := (List.all_eq_true.mp allTwo) u (List.mem_finRange u)
  have s := (List.all_eq_true.mp r) v (List.mem_finRange v)
  obtain ⟨w, _, hw⟩ := List.any_eq_true.mp s
  simp only [Bool.and_eq_true] at hw
  have h := hw
  exact ⟨w, stepB_iff.mp h.1, v, stepB_iff.mp h.2, rfl⟩

theorem noEccOne (u : Fin 11) : ¬ EccLE graph u 1 := by
  intro h
  have r := (List.all_eq_true.mp noneOne) u (List.mem_finRange u)
  obtain ⟨v, _, hv⟩ := List.any_eq_true.mp r
  obtain ⟨w, hw, hEq⟩ := h v
  change w = v at hEq
  cases hEq
  have ht := stepB_iff.mpr hw
  simp [ht] at hv

theorem allEccMore (u : Fin 11) (k : Nat) : EccLE graph u (k+2) := by
  induction k with
  | zero => exact allEccTwo u
  | succ k ih => intro v; exact (ih v).raise

theorem allCenters (u : Fin 11) : Center graph u := by
  intro w k h
  cases k with
  | zero => exact False.elim (noEccOne w (fun v => (h v).raise))
  | succ k =>
    cases k with
    | zero => exact False.elim (noEccOne w h)
    | succ k => exact allEccMore u k

def Conjecture : Prop :=
  ∀ (n : Nat) (e : Adj n), 2 ≤ n → isSimple n e = true →
    (∀ u v, ∃ k, Within e k u v) →
    ∀ (centers s : List (Fin n)), centers.Nodup →
      (∀ v, v ∈ centers ↔ Center e v) →
      s.Nodup → totallyDominates n e s = true →
        2 * centers.length ≤ s.length * maxEdgeNbr n e

theorem refutesConjecture : ¬ Conjecture := by
  intro h
  have hconn : ∀ u v, ∃ k, Within graph k u v := fun u v => ⟨2, allEccTwo u v⟩
  have hcent : ∀ v, v ∈ vertices 11 ↔ Center graph v :=
    fun v => ⟨fun _ => allCenters v, fun _ => List.mem_finRange v⟩
  exact (Nat.not_le_of_lt strictViolation)
    (h 11 graph (by decide) simple hconn (vertices 11) dominating (by decide)
      hcent domination.1 domination.2)

#print axioms refutesConjecture
#print axioms allEccTwo
#print axioms noEccOne
#print axioms edgeMaximum
end WowII255
