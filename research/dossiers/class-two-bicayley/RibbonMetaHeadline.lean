import RibbonMetaFinal
import RibbonDerivedTwoOdd

namespace RibbonMeta
open HaarClass4Structure
variable {G : Type*} [Group G]

theorem of_abelian_derived (h : IsMulCommutative (commutator G)) : Meta G := by
  rw [← Subgroup.top_lowerCentralSeries_one] at h
  have hh := isMulCommutative_iff.mp h
  intro a ha b hb
  exact congrArg Subtype.val (hh ⟨a,ha⟩ ⟨b,hb⟩)

theorem nilpotent_metabelian_ribbon [Finite G] [Group.IsNilpotent G]
    (h : IsMulCommutative (commutator G)) (x y : G)
    (odd : Odd (Nat.card G)) (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨ Ribbon.Cycle x y 32 :=
  finite_odd_nilpotent (Subgroup.nilpotent_iff_lowerCentralSeries.mp inferInstance)
    (of_abelian_derived h) x y odd hx hy

end RibbonMeta

namespace RibbonDerivedTwo
open HaarClass4Structure
variable {G : Type*} [Group G]

theorem nilpotent_ribbon_of_derived_class2 [Finite G] [Group.IsNilpotent G]
    (h : LS (commutator G) 2=⊥) (x y : G)
    (odd : Odd (Nat.card G)) (hx : x≠1) (hy : y≠1) :
    RibbonP3.Good x y := by
  obtain ⟨n,hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp
    (inferInstance : Group.IsNilpotent G)
  rw [← Subgroup.top_lowerCentralSeries_one] at h
  exact odd_nilpotent hn (of_derived_class2 h) x y odd hx hy

end RibbonDerivedTwo
#print axioms RibbonMeta.nilpotent_metabelian_ribbon
#print axioms RibbonDerivedTwo.nilpotent_ribbon_of_derived_class2
