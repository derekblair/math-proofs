import RibbonP11NormalModule
import RibbonP11Normalize
import Mathlib.Algebra.MonoidAlgebra.Basic

namespace RibbonOrder3
open RibbonAffine HaarClass4Generate HaarClass4Ports
universe u
variable {G : Type u} [Group G]

abbrev DA (G : Type u) [Group G] := Abelianization (D G)
abbrev V (G : Type u) [Group G] := Additive (DA G)

private def qConj (g : G) : DA G→*DA G :=
  Abelianization.map ((MulAut.conjNormal g).toMonoidHom)

@[simp] private theorem qConj_of (g : G) (d : D G) :
    qConj g (Abelianization.of d)=Abelianization.of (MulAut.conjNormal g d) := rfl

private def QRep : G→*Module.End ℤ (V G) where
  toFun g := (qConj g).toAdditive.toIntLinearMap
  map_one' := by
    apply LinearMap.ext
    intro d
    obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective (commutator (D G)) d.toMul
    change Additive.ofMul (qConj 1 d.toMul)=Additive.ofMul d.toMul
    have h : Abelianization.of a=d.toMul := ha
    rw [←h,qConj_of,map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro d
    obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective (commutator (D G)) d.toMul
    change Additive.ofMul (qConj (g*h) d.toMul)=Additive.ofMul (qConj g (qConj h d.toMul))
    have h' : Abelianization.of a=d.toMul := ha
    rw [←h',qConj_of,qConj_of,qConj_of,map_mul]
    rfl

private theorem action_derived (g : G) (hg : g∈D G) : QRep g=1 := by
  apply LinearMap.ext
  intro d
  obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective (commutator (D G)) d.toMul
  change Additive.ofMul (qConj g d.toMul)=Additive.ofMul d.toMul
  have h : Abelianization.of a=d.toMul := ha
  rw [←h,qConj_of]
  let z : D G := ⟨g,hg⟩
  have e : MulAut.conjNormal g a=z*a*z⁻¹ := Subtype.ext (MulAut.conjNormal_apply g a)
  apply congrArg Additive.ofMul
  rw [e,map_mul,map_mul,map_inv,mul_comm (Abelianization.of z) (Abelianization.of a),
    mul_assoc,mul_inv_cancel,mul_one]

private def abRep : Abelianization G→*Module.End ℤ (V G) :=
  QuotientGroup.lift (commutator G) QRep (fun g hg => action_derived g hg)

abbrev A (G : Type u) [Group G] := MonoidAlgebra ℤ (Abelianization G)
private noncomputable def algRep : A G→ₐ[ℤ]Module.End ℤ (V G) :=
  MonoidAlgebra.lift ℤ _ _ abRep

noncomputable instance integral_action : Module (A G) (V G) :=
  Module.compHom (V G) algRep.toRingHom

noncomputable def gin : G→*A G :=
  (MonoidAlgebra.of ℤ (Abelianization G)).comp Abelianization.of

private theorem entry (g : G) (d : V G) :
    gin g • d = Additive.ofMul (qConj g d.toMul) := by
  change (algRep (MonoidAlgebra.of ℤ _ (Abelianization.of g))) d=_
  rw [algRep,MonoidAlgebra.lift_of]
  rfl

/-- The integral cyclic action ring, with exact kernel on the derived group. -/
theorem integral_model (x y : G) (gen : Generates x y) :
    ∃ (I : Ideal (A G)) (l : D G→*Multiplicative (A G ⧸ I))
      (μ : G→*(A G ⧸ I)ˣ),
      Function.Surjective l ∧
      (∀ d, l d=1 ↔ d∈commutator (D G)) ∧
      Multiplicative.toAdd (l ⟨portC x y,layer_c x y⟩)=1 ∧
      RibbonP11.Equivariant μ l := by
  let P : D G→*Multiplicative (V G) := Abelianization.of
  have surj : Function.Surjective P := QuotientGroup.mk'_surjective _
  have cyclic := RibbonP11.cyclic_from_normal (R:=A G) (V:=V G) x y gen gin.toHomUnits P surj
    (fun g d => by
      change Additive.ofMul (Abelianization.of (MulAut.conjNormal g d)) =
        gin g • Additive.ofMul (Abelianization.of d)
      rw [entry]
      exact congrArg Additive.ofMul (qConj_of g d).symm)
  obtain ⟨I,e,E⟩ := RibbonP11.cyclic_algebra
    (Additive.ofMul (Abelianization.of (⟨portC x y,layer_c x y⟩ : D G))) cyclic
  let L := e.toAddEquiv.toAddMonoidHom.toMultiplicative.comp P
  let μ := ((Ideal.Quotient.mk I).toMonoidHom.comp gin).toHomUnits
  refine ⟨I,L,μ,e.surjective.comp surj,?_,E,fun g d => ?_⟩
  · intro d
    change e (Additive.ofMul (Abelianization.of d))=0 ↔ d∈commutator (D G)
    rw [←e.map_zero,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff _
  · change e (Additive.ofMul (Abelianization.of (MulAut.conjNormal g d))) =
      Ideal.Quotient.mk I (gin g) * e (Additive.ofMul (Abelianization.of d))
    rw [←qConj_of]
    have h := entry g (Additive.ofMul (Abelianization.of d))
    change gin g • Additive.ofMul (Abelianization.of d) =
      Additive.ofMul (qConj g (Abelianization.of d)) at h
    rw [←h,map_smul]
    rfl

end RibbonOrder3
#print axioms RibbonOrder3.integral_model
