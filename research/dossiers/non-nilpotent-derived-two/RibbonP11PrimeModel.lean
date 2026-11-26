import RibbonP11ModP
import RibbonP11Normalize

namespace RibbonP11
open RibbonAffine HaarClass4Generate HaarClass4Ports
universe u
variable {G : Type u} [Group G]

abbrev PA (G : Type u) [Group G] (p : ℕ) :=
  MonoidAlgebra (ZMod p) (Abelianization G)

noncomputable def pAlg (p : ℕ) : PA G p →ₐ[ZMod p] Module.End (ZMod p) (PV G p) :=
  MonoidAlgebra.lift (ZMod p) _ _ (pAbRep p)

noncomputable instance prime_action (p : ℕ) : Module (PA G p) (PV G p) :=
  Module.compHom (PV G p) (pAlg p).toRingHom

noncomputable def gIn (p : ℕ) : G →* PA G p :=
  (MonoidAlgebra.of (ZMod p) (Abelianization G)).comp Abelianization.of

private theorem entry (g : G) (p : ℕ) (d : PV G p) :
    (gIn p g) • d = Additive.ofMul (pConj g p d.toMul) := by
  change (pAlg p (MonoidAlgebra.of (ZMod p) _ (Abelianization.of g))) d = _
  rw [pAlg,MonoidAlgebra.lift_of]
  rfl

/-- Exact mod-p derived quotient, viewed as a cyclic quotient algebra.
The distinguished derived commutator has additive coordinate one. -/
theorem prime_model (p : ℕ) (x y : G) (gen : Generates x y) :
    ∃ (I : Ideal (PA G p))
      (e : PV G p ≃ₗ[PA G p] (PA G p ⧸ I))
      (ell : D G →* Multiplicative (PA G p ⧸ I)),
      Function.Surjective ell ∧
      (∀ d, Multiplicative.toAdd (ell d) = e (Additive.ofMul (pπ p d))) ∧
      Multiplicative.toAdd (ell ⟨portC x y,layer_c x y⟩)=1 ∧
      Equivariant (((Ideal.Quotient.mk I).toMonoidHom.comp (gIn p)).toHomUnits) ell := by
  have cyclic := cyclic_from_normal (R:=PA G p) (V:=PV G p) x y gen (gIn p).toHomUnits (pπ p)
    (pπ_surj p) (fun g d => by
      change Additive.ofMul (pπ p (MulAut.conjNormal g d)) = (gIn p g) • Additive.ofMul (pπ p d)
      rw [entry]
      exact congrArg Additive.ofMul (pConj_π g p d).symm)
  obtain ⟨I,e,E⟩ := cyclic_algebra (Additive.ofMul (pπ p ⟨portC x y,layer_c x y⟩)) cyclic
  let ell : D G →* Multiplicative (PA G p ⧸ I) :=
    e.toAddEquiv.toAddMonoidHom.toMultiplicative.comp (pπ p)
  refine ⟨I,e,ell,e.surjective.comp (pπ_surj p),fun _ => rfl,E,fun g d => ?_⟩
  change e (Additive.ofMul (pπ p (MulAut.conjNormal g d))) =
    Ideal.Quotient.mk I (gIn p g) * e (Additive.ofMul (pπ p d))
  rw [←pConj_π]
  have h := entry g p (Additive.ofMul (pπ p d))
  change (gIn p g) • Additive.ofMul (pπ p d) = Additive.ofMul (pConj g p (pπ p d)) at h
  rw [←h,map_smul]
  rfl

end RibbonP11
#print axioms RibbonP11.prime_model
