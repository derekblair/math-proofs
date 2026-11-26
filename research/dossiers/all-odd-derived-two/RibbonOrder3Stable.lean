import RibbonOrder3Affine
import RibbonStationaryThird

namespace RibbonOrder3
open RibbonAffine HaarClass4Structure HaarClass4Generate
universe u
variable {G : Type u} [Group G]

/-- Stable nonzero Γ3 in a class-two-derived odd group provides a
nontrivial residue affine chart with the existing canonical orientation. -/
theorem stable_third_affine [Finite G] (d2 : RibbonDerivedTwo.D2 G)
    (x y : G) (gen : Generates x y) (odd : Odd (Nat.card G))
    (st : LS G 2=LS G 3) (nz : LS G 2≠⊥) :
    ∃ (K : Type u) (_ : Field K) (_ : Finite K) (μ : G→*Kˣ) (τ : G→K),
      (2:K)≠0 ∧ RibbonP11.IsCocycle μ τ ∧
      RibbonP11.Normalized (RingHom.id K) x y μ τ ∧
      (μ x)^(Nat.card G)=1 ∧ (μ y)^(Nat.card G)=1 := by
  apply stable_third_affine_of_visible x y gen odd st
  rw [←Subgroup.top_lowerCentralSeries_one,Subgroup.top_subtype_lowerCentralSeries]
  exact RibbonStationaryThird.stable_third_not_in_second_derived d2 st nz

end RibbonOrder3
#print axioms RibbonOrder3.stable_third_affine
