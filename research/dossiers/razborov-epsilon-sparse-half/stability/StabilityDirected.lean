import StabilityHalfTransfer
open scoped BigOperators
namespace SparseHalfStability
variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- The directed edit budget in the finite stability theorem is exactly
twice the unordered symmetric difference for two loopless graphs. -/
theorem directed_eq_double (G H : V → V → Bool)
    (gs : ∀ a b, G a b = G b a) (hs : ∀ a b, H a b = H b a)
    (gl : ∀ a, G a a = false) (hl : ∀ a, H a a = false) :
    (directedErrors G H (fun v => v)).card =
      2*((Edges G \ Edges H) ∪ (Edges H \ Edges G)).card := by
  let B (a b : V) := decide (G a b ≠ H a b)
  have s (a b : V) : B a b = B b a := by simp [B,gs a b,hs a b]
  have l (a : V) : B a a = false := by simp [B,gl,hl]
  have h := canonical_cost B (fun _ => (1:ℝ)) s l
  have z : Edges B = (Edges G \ Edges H) ∪ (Edges H \ Edges G) := by
    apply Finset.ext
    rintro ⟨u,v⟩
    by_cases ht : u<v <;> cases hG : G u v <;> cases hH : H u v <;>
      simp [Edges,B,ht,hG,hH]
  have y : orderedCost B (fun _ => (1:ℝ)) = ((directedErrors G H (fun v => v)).card : ℝ) := by
    let f (e : V × V) : ℝ := if B e.1 e.2 then 1 else 0
    have hsum : (∑ e : V × V, f e) = ∑ a, ∑ b, f (a,b) := by
      rw [← Finset.univ_product_univ, Finset.sum_product]
    unfold orderedCost
    simp only [mul_one]
    change (∑ a, ∑ b, f (a,b)) = _
    rw [← hsum]
    change (∑ e : V × V, if B e.1 e.2 = true then (1:ℝ) else 0) = _
    simp only [B, decide_eq_true_eq, ← Finset.sum_filter]
    simp [directedErrors]
  rw [y] at h
  simp only [edgeCost,z,mul_one,Finset.sum_const,nsmul_eq_mul] at h
  exact_mod_cast h

#print axioms directed_eq_double
end SparseHalfStability
