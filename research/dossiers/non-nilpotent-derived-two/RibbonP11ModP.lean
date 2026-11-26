import RibbonP11NormalModule
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic

namespace RibbonP11
open HaarClass4Generate HaarClass4Ports RibbonAffine
variable {G : Type*} [Group G]

def powSub (A : Type*) [CommGroup A] (p : ℕ) : Subgroup A :=
  (powMonoidHom p : A →* A).range

abbrev PGroup (G : Type*) [Group G] (p : ℕ) :=
  Abelianization (D G) ⧸ powSub (Abelianization (D G)) p

def pπ (p : ℕ) : D G →* PGroup G p :=
  (QuotientGroup.mk' _).comp Abelianization.of

theorem pπ_surj (p : ℕ) : Function.Surjective (pπ (G:=G) p) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

private def abConj (g : G) : Abelianization (D G) →* Abelianization (D G) :=
  Abelianization.map (MulAut.conjNormal g).toMonoidHom

private theorem powStable (g : G) (p : ℕ) :
    powSub (Abelianization (D G)) p ≤ (powSub (Abelianization (D G)) p).comap (abConj g) := by
  rintro z ⟨a,rfl⟩
  exact ⟨abConj g a, (map_pow (abConj g) a p).symm⟩

def pConj (g : G) (p : ℕ) : PGroup G p →* PGroup G p :=
  QuotientGroup.map _ _ (abConj g) (powStable g p)

@[simp] theorem pConj_π (g : G) (p : ℕ) (d : D G) :
    pConj g p (pπ p d)=pπ p (MulAut.conjNormal g d) := rfl

theorem mod_p_pow (p : ℕ) (a : PGroup G p) : a^p=1 := by
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective _ a
  rw [←map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨b,rfl⟩

abbrev PV (G : Type*) [Group G] (p : ℕ) := Additive (PGroup G p)

noncomputable instance module_p (p : ℕ) : Module (ZMod p) (PV G p) :=
  AddCommGroup.zmodModule (fun a => mod_p_pow p a.toMul)

noncomputable def pRep (p : ℕ) : G →* Module.End (ZMod p) (PV G p) where
  toFun g := (pConj g p).toAdditive.toZModLinearMap p
  map_one' := by
    apply LinearMap.ext
    intro d
    obtain ⟨a,ha⟩ := pπ_surj p d.toMul
    change Additive.ofMul (pConj 1 p d.toMul) = Additive.ofMul d.toMul
    rw [←ha,pConj_π,map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro d
    obtain ⟨a,ha⟩ := pπ_surj p d.toMul
    change Additive.ofMul (pConj (g*h) p d.toMul) =
      Additive.ofMul (pConj g p (pConj h p d.toMul))
    rw [←ha,pConj_π,pConj_π,pConj_π,map_mul]
    rfl

private theorem pRep_derived (p : ℕ) (g : G) (hg : g∈D G) : pRep p g=1 := by
  apply LinearMap.ext
  intro d
  obtain ⟨a,ha⟩ := pπ_surj p d.toMul
  change Additive.ofMul (pConj g p d.toMul) = Additive.ofMul d.toMul
  rw [←ha,pConj_π]
  let z : D G := ⟨g,hg⟩
  have e : MulAut.conjNormal g a=z*a*z⁻¹ := Subtype.ext (MulAut.conjNormal_apply g a)
  apply congrArg Additive.ofMul
  rw [e,map_mul,map_mul,map_inv]
  rw [mul_comm (pπ p z) (pπ p a),mul_assoc,mul_inv_cancel,mul_one]

noncomputable def pAbRep (p : ℕ) : Abelianization G →* Module.End (ZMod p) (PV G p) :=
  QuotientGroup.lift (commutator G) (pRep p) (fun g hg => pRep_derived p g hg)

end RibbonP11
#print axioms RibbonP11.pAbRep
