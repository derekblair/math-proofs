import QuadraticAnswer

namespace QuadraticCA

/-- The obstruction does not rule out affine proper liftings. -/
theorem first_coordinate_is_proper :
    ∀ n, 1 ≤ n → Function.Bijective (@ringLift 1 n (fun v => v 0)) := by
  intro n hn
  have e : (@ringLift 1 n (fun v => v 0)) = id := by
    funext x i
    have h : (⟨(i.val + (0 : Fin 1).val) % n,
      Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩ : Fin n) = i := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt i.isLt]
    exact congrArg x h
  rw [e]
  exact Function.bijective_id

/-- For the single quadratic monomial, two distinct words on a four-cell ring
produce the same output directly, without using the main theorem. -/
example :
    ¬ Function.Injective (@ringLift 2 4 (fun v => v 0 * v 1)) := by decide

end QuadraticCA
