import NeutralAffineExact

namespace NeutralReachable
open NeutralAffineExact TripTrace AffineAddress IntegerEigen

def D : Finset ℤ := {-1,0,1}
def f (x : ℤ) : List ℤ := if x=0 then [0,1,-1] else if x=1 then [1,0,0,0] else [-1,0]

theorem closed : ∀ x ∈ D, ∀ y ∈ f x, y∈D := by
  intro x hx y hy
  simp [D] at hx
  rcases hx with rfl | rfl | rfl <;> simp [f] at hy <;> (rcases hy with rfl | rfl | rfl) <;> decide

theorem aff : ∀ x ∈ D, σ (f x) = mat 3 1 0 1 (σ [x]) := by
  intro x hx
  simp [D] at hx
  rcases hx with rfl | rfl | rfl <;> decide

theorem doubles (w : List ℤ) : 2*w.length ≤ (w.flatMap f).length := by
  induction w with
  | nil => simp
  | cons x w ih =>
    have h : 2 ≤ (f x).length := by
      unfold f
      split
      · decide
      · split <;> decide
    simp only [List.length_cons,List.flatMap_cons,List.length_append]
    omega

theorem lt_iter (n : ℕ) : n < (iter f 0 n).length := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := doubles (iter f 0 n)
    change n+1 < ((iter f 0 n).flatMap f).length
    omega

theorem all_reachable : ∀ x ∈ D, x ∈ iter f 0 1 := by
  intro x hx
  simp [D] at hx
  rcases hx with rfl | rfl | rfl <;> decide

theorem positive : calculate D f closed 3 1 0 1 false 0 (by decide) = true := by
  apply (calculate_correct D f closed 3 1 0 1 false aff (by decide) (by decide)
    0 (by decide) [1,-1] (by decide) (fun n => ⟨n,lt_iter n⟩)).mpr
  exact ⟨2,[0,1,-1,1],[0],[0],[0,-1,0],by decide,by decide,by decide,by decide⟩

end NeutralReachable

#print axioms NeutralReachable.all_reachable
#print axioms NeutralReachable.positive
