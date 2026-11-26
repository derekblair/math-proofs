import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace RepairCausal

/-- Within a fixed earlier-pad value, full support invariance contains a
translated copy of all fresh prefix directions. Their distribution, if
invariant, has equal mass along each such orbit. -/
theorem fibre_translate {A B : Type*} [AddGroup A] [AddGroup B]
    (p : A →+ B) (K : AddSubgroup A) (zeroProj : K ≤ p.ker)
    (support : Set A) (anchor : A) (inside : anchor ∈ support)
    (inv : ∀ x ∈ support, ∀ k ∈ K, x+k ∈ support) :
    Nonempty (K ↪ {x : A // x ∈ support ∧ p x = p anchor}) := by
  refine ⟨⟨fun k => ⟨anchor+k, inv anchor inside k k.property, ?_⟩, ?_⟩⟩
  · rw [map_add, show p k = 0 from zeroProj k.property, add_zero]
  · intro x y eq
    apply Subtype.ext
    exact add_left_cancel (congrArg Subtype.val eq)

/-- Conditioning one public repair value removes exactly its rank from fresh
increment directions. This is the local summand in the optimal causal budget. -/
theorem increment_kernel_dim {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (eval : V →ₗ[F] F) :
    Module.finrank F eval.ker = Module.finrank F V - Module.finrank F eval.range := by
  have h := LinearMap.finrank_range_add_finrank_ker eval
  omega

#print axioms fibre_translate
#print axioms increment_kernel_dim
end RepairCausal
