import RibbonP11CyclicModule
import RibbonAffineCocycle

namespace RibbonP11
open RibbonAffine HaarClass4Generate HaarClass4Ports
variable {G R V : Type*} [Group G] [CommRing R] [AddCommGroup V] [Module R V]

/-- Any equivariant additive quotient of the derived group is cyclic over
the acting commutative ring. Surjectivity and normal generation are what
transfer the two-generator hypothesis to the module. -/
theorem cyclic_from_normal (x y : G) (gen : Generates x y)
    (act : G →* Rˣ) (ell : D G →* Multiplicative V) (onto : Function.Surjective ell)
    (equiv : ∀ g d, Multiplicative.toAdd (ell (MulAut.conjNormal g d)) =
      (act g : R) • Multiplicative.toAdd (ell d)) :
    Function.Surjective (LinearMap.toSpanSingleton R V
      (Multiplicative.toAdd (ell ⟨portC x y,layer_c x y⟩))) := by
  let d : D G := ⟨portC x y,layer_c x y⟩
  let c := Multiplicative.toAdd (ell d)
  let P := Submodule.span R {c}
  let Q : Subgroup (D G) :=
    { carrier := {d' | Multiplicative.toAdd (ell d') ∈ P}
      one_mem' := by
        change Multiplicative.toAdd (ell 1) ∈ P
        rw [map_one]
        exact P.zero_mem
      mul_mem' := by
        intro a b ha hb
        change Multiplicative.toAdd (ell (a*b)) ∈ P
        rw [map_mul]
        exact P.add_mem ha hb
      inv_mem' := by
        intro a ha
        change Multiplicative.toAdd (ell a⁻¹) ∈ P
        rw [map_inv]
        exact P.neg_mem ha }
  let N := Q.map (D G).subtype
  letI : N.Normal := by
    constructor
    intro a ha g
    obtain ⟨b,hb,rfl⟩ := ha
    refine ⟨MulAut.conjNormal g b,?_,MulAut.conjNormal_apply g b⟩
    change Multiplicative.toAdd (ell (MulAut.conjNormal g b)) ∈ P
    rw [equiv]
    exact P.smul_mem _ hb
  have hc : portC x y ∈ N := ⟨d,Submodule.mem_span_singleton_self c,rfl⟩
  have cN : D G ≤ N := by
    rw [←normalClosure_c x y gen]
    apply Subgroup.normalClosure_le_normal
    exact Set.singleton_subset_iff.mpr (show portC x y ∈ (N : Set G) from hc)
  have pTop : P=⊤ := by
    apply top_unique
    intro v _
    obtain ⟨k,hk⟩ := onto (Multiplicative.ofAdd v)
    have H := cN k.property
    obtain ⟨b,hb,eq⟩ := H
    have B : b=k := Subtype.ext eq
    subst b
    change Multiplicative.toAdd (ell k) ∈ P at hb
    rw [hk] at hb
    exact hb
  change Function.Surjective (LinearMap.toSpanSingleton R V c)
  rw [← LinearMap.range_eq_top,← LinearMap.span_singleton_eq_range]
  exact pTop

end RibbonP11
#print axioms RibbonP11.cyclic_from_normal
