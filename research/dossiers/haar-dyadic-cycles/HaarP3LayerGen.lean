import HaarClass4Generate

namespace HaarP3LayerGen

open scoped commutatorElement
open HaarClass4Structure HaarClass4Ports HaarClass4Generate

variable {G : Type*} [Group G]

theorem ls3_bot_of_center_uv (x y : G) (gen : Generates x y)
    (hu : portU x y ∈ Subgroup.center G) (hv : portV x y ∈ Subgroup.center G) :
    LS G 3 = ⊥ := by
  let S := Subgroup.center G
  let φ := QuotientGroup.mk' S
  have cu : φ (portU x y) = 1 := (QuotientGroup.eq_one_iff _).mpr hu
  have cv : φ (portV x y) = 1 := (QuotientGroup.eq_one_iff _).mpr hv
  have cx : Commute (φ (portC x y)) (φ x) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa [portU,map_commutatorElement] using cu
  have cy : Commute (φ (portC x y)) (φ y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa [portV,map_commutatorElement] using cv
  have hxy : φ x * φ y = φ y * φ x * φ (portC x y) := by
    simpa using congrArg φ (ports_xy x y)
  have gg := map_gen φ (QuotientGroup.mk'_surjective S) gen
  have z := c_center_class_two _ _ _ gg hxy (gen_center _ _ _ gg cx cy)
  have m := map_ls φ (QuotientGroup.mk'_surjective S) 2
  rw [z, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at m
  exact Subgroup.lowerCentralSeries_succ_eq_bot ⊤ m

theorem ls3_eq_tail_closure (h : LS G 4 = ⊥) (x y : G) (gen : Generates x y) :
    LS G 3 = Subgroup.closure
      ({(make h x y).a,(make h x y).b,(make h x y).d} : Set G) := by
  let E := make h x y
  let S := Subgroup.closure ({E.a,E.b,E.d} : Set G)
  have hla : E.a ∈ LS G 3 := (tail_layers h x y).1
  have hlb : E.b ∈ LS G 3 := (tail_layers h x y).2.1
  have hld : E.d ∈ LS G 3 := (tail_layers h x y).2.2
  have hS : S ≤ LS G 3 := (Subgroup.closure_le _).mpr (by
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl <;> assumption)
  let : S.Normal := Subgroup.normal_of_le_center (hS.trans (layer4_center h))
  let φ := QuotientGroup.mk' S
  have ha : φ E.a = 1 := (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.subset_closure (by simp))
  have hb : φ E.b = 1 := (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.subset_closure (by simp))
  have hd : φ E.d = 1 := (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.subset_closure (by simp))
  have cuX : Commute (φ E.u) (φ x) := by
    change φ E.u * φ E.x = φ E.x * φ E.u
    simpa [ha] using congrArg φ E.ux
  have cuY : Commute (φ E.u) (φ y) := by
    change φ E.u * φ E.y = φ E.y * φ E.u
    simpa [hb] using congrArg φ E.uy
  have cvX : Commute (φ E.v) (φ x) := by
    change φ E.v * φ E.x = φ E.x * φ E.v
    simpa [hb] using congrArg φ E.vx
  have cvY : Commute (φ E.v) (φ y) := by
    change φ E.v * φ E.y = φ E.y * φ E.v
    simpa [hd] using congrArg φ E.vy
  have gg := map_gen φ (QuotientGroup.mk'_surjective S) gen
  have hu' : portU (φ x) (φ y) ∈ Subgroup.center (G ⧸ S) := by
    have eq : φ E.u = portU (φ x) (φ y) := by
      change φ (portU x y) = _
      simp [portU,portC,map_commutatorElement]
    exact eq ▸ gen_center _ _ _ gg cuX cuY
  have hv' : portV (φ x) (φ y) ∈ Subgroup.center (G ⧸ S) := by
    have eq : φ E.v = portV (φ x) (φ y) := by
      change φ (portV x y) = _
      simp [portV,portC,map_commutatorElement]
    exact eq ▸ gen_center _ _ _ gg cvX cvY
  have m := map_ls φ (QuotientGroup.mk'_surjective S) 3
  rw [ls3_bot_of_center_uv _ _ gg hu' hv', Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at m
  exact le_antisymm m hS

end HaarP3LayerGen

#print axioms HaarP3LayerGen.ls3_eq_tail_closure
