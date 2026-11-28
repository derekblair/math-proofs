import Lean.Elab.Tactic.Omega

namespace Erdős151.H12

universe u
variable {V : Type u}

/-- Extend given colors on rank-zero vertices, following a selected
out-neighbor of strictly smaller rank at every other vertex. -/
def extendColor (rank : V → Nat) (next : V → V)
    (drops : ∀ v, rank v ≠ 0 → rank (next v) < rank v)
    (base : V → Bool) (v : V) : Bool :=
  if _h : rank v = 0 then base v else !extendColor rank next drops base (next v)
termination_by rank v
decreasing_by exact drops v _h

theorem extendColor_opposite (rank : V → Nat) (next : V → V)
    (drops : ∀ v, rank v ≠ 0 → rank (next v) < rank v)
    (base : V → Bool)
    (atZero : ∀ v, rank v = 0 → rank (next v) = 0 ∧ base v ≠ base (next v))
    (v : V) : extendColor rank next drops base v ≠ extendColor rank next drops base (next v) := by
  by_cases hv : rank v = 0
  · have hh := atZero v hv
    have e0 : extendColor rank next drops base v = base v := by
      rw [extendColor]; simp [hv]
    have e1 : extendColor rank next drops base (next v) = base (next v) := by
      rw [extendColor]; simp [hh.1]
    simpa only [e0,e1] using hh.2
  · have e0 : extendColor rank next drops base v =
        !extendColor rank next drops base (next v) := by
      rw [extendColor]; simp [hv]
    exact fun h => by
      rw [e0] at h
      exact (show ∀ b : Bool, (!b) ≠ b by decide) _ h

/-- Finite balanced incidence setup after choosing a perfect matching.
Each indexed constraint includes its own vertex and a selected alternate
vertex. Once those selections have an even-cycle rank structure, every
constraint has both colors. -/
theorem ranked_two_color (rank : V → Nat) (next : V → V)
    (drops : ∀ v, rank v ≠ 0 → rank (next v) < rank v)
    (base : V → Bool)
    (atZero : ∀ v, rank v = 0 → rank (next v) = 0 ∧ base v ≠ base (next v)) :
    ∃ c : V → Bool, ∀ v, c v ≠ c (next v) :=
  ⟨extendColor rank next drops base, extendColor_opposite rank next drops base atZero⟩

#print axioms extendColor_opposite
#print axioms ranked_two_color
end Erdős151.H12
