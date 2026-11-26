import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.GroupTheory.Index

namespace RibbonAffine
open scoped MonoidAlgebra

universe u v
variable {A : Type u} {V : Type v} [CommGroup A] [AddCommGroup V] [Finite V] [Nontrivial V]

set_option maxHeartbeats 800000

/-- A finite nonzero module for a commuting group action has a scalar
quotient over a finite field, using a maximal submodule of ℤ[A]. -/
theorem scalar_quotient (ρ : A →* Module.End ℤ V) :
    ∃ (K : Type u) (_ : Field K) (_ : Finite K)
      (μ : A →* Kˣ) (ell : V →+ K), Function.Surjective ell ∧
      (∀ a d, ell (ρ a d) = (μ a : K)*ell d) := by
  classical
  let R := MonoidAlgebra ℤ A
  let M := V
  let alg : R →ₐ[ℤ] Module.End ℤ V := MonoidAlgebra.lift ℤ _ A ρ
  letI : Module R M := Module.compHom V alg.toRingHom
  letI : Finite (Submodule R M) := Finite.of_injective (fun s : Submodule R M => (s : Set M))
    SetLike.coe_injective
  have hbot : (⊥ : Submodule R M) ≠ ⊤ := bot_ne_top
  obtain ⟨W,cW⟩ := IsCoatomic.exists_coatom (α:=Submodule R M)
  have S : IsSimpleModule R (M ⧸ W) := isSimpleModule_iff_isCoatom.mpr cW
  obtain ⟨I,hI,⟨lin⟩⟩ := isSimpleModule_iff_quot_maximal.mp S
  letI : I.IsMaximal := hI
  let K := R ⧸ I
  letI : Field K := Ideal.Quotient.field I
  let p := lin.toLinearMap.comp W.mkQ
  have ps : Function.Surjective p := lin.surjective.comp W.mkQ_surjective
  let ell : V →+ K := p.toAddMonoidHom
  have es : Function.Surjective ell := ps
  letI : Finite K := Finite.of_surjective ell es
  let φ : A →* K := (Ideal.Quotient.mk I).toMonoidHom.comp (MonoidAlgebra.of ℤ A)
  let μ := φ.toHomUnits
  refine ⟨K,inferInstance,inferInstance,μ,ell,es,fun a d => ?_⟩
  have act : ρ a d = MonoidAlgebra.of ℤ A a • (d : M) := by
    change ρ a d = alg (MonoidAlgebra.of ℤ A a) d
    rw [MonoidAlgebra.lift_of]
  change p (ρ a d) = φ a * p d
  rw [act,map_smul]
  rfl

end RibbonAffine
#print axioms RibbonAffine.scalar_quotient
