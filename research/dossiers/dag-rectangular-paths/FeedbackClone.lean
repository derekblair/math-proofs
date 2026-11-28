import Std

namespace SparseDAG.FeedbackClone

inductive Vertex (V : Type) where
  | old : V → Vertex V
  | enter : V → Vertex V
  | leave : V → Vertex V
  deriving DecidableEq

variable {V : Type}
def erase : Vertex V → V
  | .old v | .enter v | .leave v => v
def tail (cut : V → Bool) (v : V) : Vertex V :=
  if cut v then .leave v else .old v
def head (cut : V → Bool) (v : V) : Vertex V :=
  if cut v then .enter v else .old v

@[simp] theorem erase_tail (cut : V → Bool) (v : V) : erase (tail cut v) = v := by
  unfold tail
  split <;> rfl
@[simp] theorem erase_head (cut : V → Bool) (v : V) : erase (head cut v) = v := by
  unfold head
  split <;> rfl

/-- Consecutive lifted edges can meet only at the same uncut vertex. -/
theorem head_eq_tail (cut : V → Bool) (u v : V) :
    head cut u = tail cut v ↔ u = v ∧ cut v = false := by
  constructor
  · intro h
    have eq : u = v := by simpa using congrArg erase h
    subst u
    by_cases hv : cut v
    · simp [hv, head, tail] at h
    · simp [hv]
  · rintro ⟨rfl, hv⟩
    simp [hv, head, tail]

/-- No clone of a cut vertex can be traversed as an intermediate node. -/
theorem intermediate_uncut (cut : V → Bool) (a b : V) (x : Vertex V)
    (arrives : head cut a = x) (leaves : tail cut b = x) :
    a = b ∧ cut b = false ∧ x = .old b := by
  obtain ⟨eq, hb⟩ := (head_eq_tail cut a b).mp (arrives.trans leaves.symm)
  exact ⟨eq, hb, by simpa [tail,hb] using leaves.symm⟩

def used (cut : V → Bool) (v : Vertex V) : Prop :=
  match v with
  | .old x => cut x = false
  | .enter x | .leave x => cut x = true

/-- Any collision after projection of distinct used labels is exactly
the two endpoint copies of a single assigned cut vertex. -/
theorem erase_collision (cut : V → Bool) (x y : Vertex V)
    (hx : used cut x) (hy : used cut y) (eq : erase x = erase y) :
    x = y ∨ ∃ u, cut u = true ∧
      ((x = .enter u ∧ y = .leave u) ∨ (x = .leave u ∧ y = .enter u)) := by
  cases x <;> cases y <;> simp only [erase] at eq <;> subst_vars <;>
    simp_all [used]

def rank (r : V → Nat) (bound : Nat) : Vertex V → Nat
  | .leave _ => 0
  | .old x => 1 + r x
  | .enter _ => bound + 2

/-- Every lifted edge increases a common topological rank. -/
theorem lift_inc (cut : V → Bool) (r : V → Nat) (bound : Nat)
    (rb : ∀ v, r v ≤ bound) {u v : V}
    (inc : cut u = false → cut v = false → r u < r v) :
    rank r bound (tail cut u) < rank r bound (head cut v) := by
  cases hu : cut u <;> cases hv : cut v <;> simp [tail,head,hu,hv,rank]
  · exact inc hu hv
  · have h := rb u
    omega
  · omega

#print axioms head_eq_tail
#print axioms intermediate_uncut
#print axioms erase_collision
#print axioms lift_inc
end SparseDAG.FeedbackClone
