import RibbonMetaDrop
import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace RibbonP11
open HaarClass4Structure HaarClass4Ports HaarClass4Generate
open scoped commutatorElement
variable {G : Type*} [Group G]

private theorem class2_cyclic_abelianization (nil : LS G 2=⊥)
    [IsCyclic (Abelianization G)] : IsMulCommutative G := by
  let Z := Subgroup.center G
  let f := QuotientGroup.mk' Z
  have le : commutator G ≤ Z := by
    change LS G 1 ≤ Z
    intro g hg
    apply Subgroup.mem_center_iff.mpr
    intro w
    have e := next_layer hg w
    rw [nil,Subgroup.mem_bot] at e
    exact (commutatorElement_eq_one_iff_commute.mp e).symm.eq
  let p : Abelianization G →* (G ⧸ Z) :=
    QuotientGroup.lift (commutator G) f (by rwa [QuotientGroup.ker_mk'])
  have onto : Function.Surjective p := by
    intro v
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective Z v
    exact ⟨Abelianization.of g,rfl⟩
  letI : IsCyclic (G ⧸ Z) := isCyclic_of_surjective p onto
  letI : CommGroup G := commGroupOfCyclicCenterQuotient f (by rw [QuotientGroup.ker_mk'])
  infer_instance

/-- A nilpotent group with cyclic abelianization is cyclic. -/
theorem cyclic_of_abelianization (nil : ∃ n, LS G n=⊥) [IsCyclic (Abelianization G)] :
    IsCyclic G := by
  obtain ⟨n,hn⟩ := nil
  let S := LS G 2
  let f := QuotientGroup.mk' S
  have surj := QuotientGroup.mk'_surjective S
  let q : Abelianization G →* Abelianization (G ⧸ S) := Abelianization.map f
  have qs : Function.Surjective q := by
    intro v
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (commutator (G ⧸ S)) v
    obtain ⟨g,rfl⟩ := surj u
    exact ⟨Abelianization.of g,rfl⟩
  letI : IsCyclic (Abelianization (G ⧸ S)) := isCyclic_of_surjective q qs
  have nilS : LS (G ⧸ S) 2=⊥ := by
    rw [←map_ls f surj 2,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  letI : IsMulCommutative (G ⧸ S) := class2_cyclic_abelianization nilS
  have zero : LS (G ⧸ S) 1=⊥ :=
    Subgroup.top_lowerCentralSeries_one.trans (commutator_eq_bot _)
  have h := map_ls f surj 1
  rw [zero,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at h
  have same : LS G 1=LS G 2 := le_antisymm h
    (Subgroup.lowerCentralSeries_antitone ⊤ (by decide : 1≤2))
  have comm : commutator G=⊥ :=
    Subgroup.top_lowerCentralSeries_one.symm.trans (RibbonMeta.lower_drop hn same)
  apply isCyclic_of_injective Abelianization.of
  rw [←MonoidHom.ker_eq_bot_iff,Abelianization.ker_of,comm]

end RibbonP11
#print axioms RibbonP11.cyclic_of_abelianization
