import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

namespace RibbonP11
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A cyclic module over a commutative ring inherits a quotient-algebra
coordinate in which its designated generator is exactly one. -/
theorem cyclic_algebra (c : M) (h : Function.Surjective (LinearMap.toSpanSingleton R M c)) :
    ∃ (I : Ideal R) (e : M ≃ₗ[R] R ⧸ I), e c=1 := by
  let f := LinearMap.toSpanSingleton R M c
  let I : Ideal R := LinearMap.ker f
  let e : (R ⧸ I) ≃ₗ[R] M := LinearMap.quotKerEquivOfSurjective f h
  refine ⟨I,e.symm,?_⟩
  apply e.injective
  rw [LinearEquiv.apply_symm_apply]
  exact ((LinearMap.quotKerEquivOfSurjective_apply_mk f h 1).trans
    (by change (1:R) • c = c; exact one_smul _ _)).symm

end RibbonP11
#print axioms RibbonP11.cyclic_algebra
