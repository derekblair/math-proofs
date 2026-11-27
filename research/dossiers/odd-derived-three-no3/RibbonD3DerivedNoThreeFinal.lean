import RibbonD3DerivedNoThreeStationary
import RibbonAffineFinal

namespace RibbonD3DerivedNoThree
open RibbonDerived3
universe u

private theorem metab : RibbonP11.MetaCover.{u} := by
  intro G _ _ m x y odd hx hy
  have h : IsMulCommutative (commutator G) := by
    rw [← Subgroup.top_lowerCentralSeries_one]
    refine ⟨⟨?_⟩⟩
    intro a b
    exact Subtype.ext (m a a.property b b.property).eq
  have C := RibbonAffine.finite_odd_metabelian_ribbon h x y odd hx hy
  exact C.imp_right (fun r => r.imp_right (fun s => s.imp_right Or.inl))

/-- Odd groups with three-free derived order, conditional only on noncharacteristic-three charts, pairs, and jets. -/
theorem finite_odd_derived_three_no3_of_covers {G : Type u} [Group G] [Finite G]
    {Bad : RibbonD3Odd.Triple→Prop} (no3 : GoodDerived G)
    (fields : RibbonD3Odd.FieldCover.{u,u} Bad) (pairs : RibbonD3Odd.PairCover.{u} Bad) (jets : RibbonD3Odd.JetCover.{u} Bad)
    (d3 : DLS G 3=⊥) (x y : G) (odd : Odd (Nat.card G)) (hx : x≠1) (hy : y≠1) :
    RibbonD3Odd.WideGood x y :=
  from_covers no3 fields pairs jets metab d3 x y odd hx hy

#print axioms finite_odd_derived_three_no3_of_covers
end RibbonD3DerivedNoThree
