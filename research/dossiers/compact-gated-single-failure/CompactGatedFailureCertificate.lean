import Mathlib.Tactic.Linarith

namespace CompactGatedFailure

inductive Copy where
  | gateOut
  | core (i : ℕ)
  | gateIn

def splitRank (n : ℕ) : Copy → ℕ
  | .gateOut => 0
  | .core i => i + 1
  | .gateIn => n + 1

inductive Allowed (n : ℕ) : Copy → Copy → Prop where
  | outCore (i : ℕ) : Allowed n .gateOut (.core i)
  | outIn : Allowed n .gateOut .gateIn
  | coreCore (i j : ℕ) (h : i < j) : Allowed n (.core i) (.core j)
  | coreIn (i : ℕ) (h : i < n) : Allowed n (.core i) .gateIn

theorem split_ranks_increase {n : ℕ} {u v : Copy} (h : Allowed n u v) :
    splitRank n u < splitRank n v := by
  cases h <;> simp [splitRank, *]

def pathWeight {V : Type*} (w : V → V → ℤ) : V → List V → ℤ
  | _, [] => 0
  | a, b :: bs => w a b + pathWeight w b bs

def endpoint {V : Type*} : V → List V → V
  | a, [] => a
  | _, b :: bs => endpoint b bs

theorem potential_stitches {V : Type*} (w : V → V → ℤ) (h : V → ℤ)
    (a : V) (rest : List V) :
    pathWeight (fun u v => w u v + h u - h v) a rest =
      pathWeight w a rest + h a - h (endpoint a rest) := by
  induction rest generalizing a with
  | nil => simp [pathWeight, endpoint]
  | cons b bs ih =>
    simp only [pathWeight, endpoint, ih b]
    omega

theorem closed_walk_weight_preserved {V : Type*} (w : V → V → ℤ)
    (h : V → ℤ) (a : V) (rest : List V) (closed : endpoint a rest = a) :
    pathWeight (fun u v => w u v + h u - h v) a rest =
      pathWeight w a rest := by
  rw [potential_stitches, closed]
  omega

theorem global_labels_feasible {V : Type*} (w : V → V → ℤ) (d : V → ℤ)
    (u v : V) (triangle : d v ≤ d u + w u v) :
    0 ≤ w u v + d u - d v := by omega

#print axioms split_ranks_increase
#print axioms potential_stitches
#print axioms closed_walk_weight_preserved
#print axioms global_labels_feasible

end CompactGatedFailure
