import HaarP3LayerGen

namespace HaarP3LayerGen

open scoped commutatorElement
open HaarClass4Structure HaarClass4Ports HaarClass4Generate
variable {G : Type*} [Group G]

theorem ls2_eq_uv_closure_of_class3 (h : LS G 3 = ⊥) (x y : G) (gen : Generates x y) :
    LS G 2 = Subgroup.closure ({portU x y,portV x y} : Set G) := by
  let S := Subgroup.closure ({portU x y,portV x y} : Set G)
  have inc : S ≤ LS G 2 := (Subgroup.closure_le _).mpr (by
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact layer_u x y
    · exact layer_v x y)
  have center : LS G 2 ≤ Subgroup.center G :=
    Subgroup.commutator_top_right_eq_bot_iff_le_center.mp h
  let : S.Normal := Subgroup.normal_of_le_center (inc.trans center)
  let φ := QuotientGroup.mk' S
  have u : φ (portU x y) = 1 := (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.subset_closure (by simp))
  have v : φ (portV x y) = 1 := (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.subset_closure (by simp))
  have cx : Commute (φ (portC x y)) (φ x) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa [portU,map_commutatorElement] using u
  have cy : Commute (φ (portC x y)) (φ y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa [portV,map_commutatorElement] using v
  have e : φ x * φ y = φ y * φ x * φ (portC x y) := by
    simpa using congrArg φ (ports_xy x y)
  have gg := map_gen φ (QuotientGroup.mk'_surjective S) gen
  have z := c_center_class_two _ _ _ gg e (gen_center _ _ _ gg cx cy)
  have m := map_ls φ (QuotientGroup.mk'_surjective S) 2
  rw [z, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at m
  exact le_antisymm m inc

theorem ls2_mod_ls3 (x y : G) (gen : Generates x y) :
    let φ := QuotientGroup.mk' (LS G 3)
    (LS G 2).map φ = Subgroup.closure ({φ (portU x y),φ (portV x y)} : Set (G ⧸ LS G 3)) := by
  let φ := QuotientGroup.mk' (LS G 3)
  change (LS G 2).map φ = _
  have onto := QuotientGroup.mk'_surjective (LS G 3)
  have z : LS (G ⧸ LS G 3) 3 = ⊥ := by
    rw [← map_ls φ onto, Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  rw [map_ls φ onto,ls2_eq_uv_closure_of_class3 z _ _ (map_gen φ onto gen)]
  change Subgroup.closure ({portU (φ x) (φ y),portV (φ x) (φ y)} : Set (G ⧸ LS G 3)) =
    Subgroup.closure ({φ (portU x y),φ (portV x y)} : Set (G ⧸ LS G 3))
  simp only [portU,portV,portC,map_commutatorElement,map_inv]

end HaarP3LayerGen

#print axioms HaarP3LayerGen.ls2_mod_ls3
