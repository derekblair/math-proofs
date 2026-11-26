import RibbonOrder3Integral
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace RibbonOrder3
open RibbonAffine HaarClass4Structure RibbonP11
open scoped commutatorElement
variable {G R : Type*} [Group G] [CommRing R]

def aug (μ : G→*Rˣ) : Ideal R :=
  Ideal.span {r | ∃ g, r=1-(μ g:R)}

def third (ell : D G→*Multiplicative R) : Ideal R :=
  Ideal.span { r | ∃ d : D G, d.val∈LS G 2 ∧ r=Multiplicative.toAdd (ell d) }

private theorem L2_in_D (G : Type*) [Group G] : LS G 2 ≤ D G :=
  Subgroup.lowerCentralSeries_antitone ⊤ (by decide : 1≤2)

/-- Lower-central stabilization puts the image of Γ3 inside its product
by the augmentation ideal. No assertion about reduction mod p is needed. -/
theorem stable_smul (μ : G→*Rˣ) (ell : D G→*Multiplicative R)
    (eq : Equivariant μ ell) (st : LS G 2=LS G 3) :
    third ell ≤ (aug μ) • third ell := by
  rw [Ideal.smul_eq_mul]
  let I := aug μ * third ell
  let f := Ideal.Quotient.mk I
  let P := f.toAddMonoidHom.toMultiplicative.comp ell
  let N := P.ker.map (D G).subtype
  have L : LS G 3 ≤ N := by
    change ⁅LS G 2,(⊤ : Subgroup G)⁆ ≤ _
    apply Subgroup.commutator_le.mpr
    intro d hd s _
    refine ⟨cAt d s,?_,rfl⟩
    change f (disp ell s d)=0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [disp_derived μ ell eq s (⟨d,L2_in_D G hd⟩ : D G)]
    apply Ideal.mul_mem_mul
    · exact Ideal.subset_span ⟨s,rfl⟩
    · exact Ideal.subset_span ⟨⟨d,L2_in_D G hd⟩,hd,rfl⟩
  apply Ideal.span_le.mpr
  intro a ha
  obtain ⟨d,hd,rfl⟩ := ha
  have hN : d.val∈N := L (st ▸ hd)
  obtain ⟨w,hw,E⟩ := hN
  have desc : w=d := Subtype.ext E
  subst w
  change f (Multiplicative.toAdd (ell d))=0 at hw
  exact Ideal.Quotient.eq_zero_iff_mem.mp hw

/-- Nakayama forces a genuine nontrivial residue character, not merely
a tangent direction, whenever the stable image is nonzero. -/
theorem nontrivial_residue [Finite R] (μ : G→*Rˣ) (ell : D G→*Multiplicative R)
    (eq : Equivariant μ ell) (st : LS G 2=LS G 3)
    (nz : ∃ d : D G, d.val∈LS G 2 ∧ ell d≠1) :
    ∃ L : Ideal R, L.IsMaximal ∧ ∃ s : G, Ideal.Quotient.mk L (μ s:R)≠1 := by
  classical
  by_contra! no
  have jac : aug μ ≤ (⊥ : Ideal R).jacobson := by
    change aug μ ≤ sInf {L : Ideal R | ⊥ ≤ L ∧ L.IsMaximal}
    apply le_sInf
    intro L hL
    apply Ideal.span_le.mpr
    intro r hr
    obtain ⟨g,rfl⟩ := hr
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub,map_one,no L hL.2 g,sub_self]
  have fg : (third ell).FG := by
    change Submodule.FG (third ell : Submodule R R)
    rw [Submodule.fg_def]
    exact ⟨third ell,Set.toFinite _,Submodule.span_eq _⟩
  have Z := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (aug μ) (third ell) fg
    (stable_smul μ ell eq st) jac
  obtain ⟨d,hd,nd⟩ := nz
  apply nd
  have H : Multiplicative.toAdd (ell d)∈third ell := Ideal.subset_span ⟨d,hd,rfl⟩
  rw [Z,Submodule.mem_bot] at H
  exact H

end RibbonOrder3
#print axioms RibbonOrder3.nontrivial_residue
