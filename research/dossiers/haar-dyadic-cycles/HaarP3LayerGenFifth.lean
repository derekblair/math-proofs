import HaarP3LayerGenBridge

namespace HaarP3LayerGen

open scoped commutatorElement
open HaarClass4Structure HaarClass4Ports HaarClass4Generate
variable {G : Type*} [Group G]

theorem ls4_center_of_class5 (nil : LS G 5=⊥) :
    LS G 4 ≤ Subgroup.center G :=
  Subgroup.commutator_top_right_eq_bot_iff_le_center.mp nil

theorem ls4_eq_two_closure (nil : LS G 5=⊥) (x y a : G) (gen : Generates x y)
    (ha : a ∈ LS G 3)
    (span : let f := QuotientGroup.mk' (LS G 4); (LS G 3).map f = Subgroup.zpowers (f a)) :
    LS G 4 = Subgroup.closure ({⁅a,x⁆,⁅a,y⁆} : Set G) := by
  let f := QuotientGroup.mk' (LS G 4)
  change (LS G 3).map f = Subgroup.zpowers (f a) at span
  let S := Subgroup.closure ({⁅a,x⁆,⁅a,y⁆} : Set G)
  have hS : S ≤ LS G 4 := (Subgroup.closure_le _).mpr (by
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact next_layer ha x
    · exact next_layer ha y)
  let : S.Normal := Subgroup.normal_of_le_center (hS.trans (ls4_center_of_class5 nil))
  let φ := QuotientGroup.mk' S
  have hx : φ ⁅a,x⁆=1 := (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.subset_closure (by simp))
  have hy : φ ⁅a,y⁆=1 := (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.subset_closure (by simp))
  have cx : Commute (φ a) (φ x) := commutatorElement_eq_one_iff_commute.mp
    ((map_commutatorElement φ a x).symm.trans hx)
  have cy : Commute (φ a) (φ y) := commutatorElement_eq_one_iff_commute.mp
    ((map_commutatorElement φ a y).symm.trans hy)
  have onto := QuotientGroup.mk'_surjective S
  have ac := gen_center _ _ _ (map_gen φ onto gen) cx cy
  have all : (LS G 3).map φ ≤ Subgroup.center (G ⧸ S) := by
    rintro _ ⟨z,hz,rfl⟩
    have zm : f z ∈ (LS G 3).map f := Subgroup.mem_map_of_mem f hz
    rw [span] at zm
    obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp zm
    let t := (a^n)⁻¹*z
    have ht : t ∈ LS G 4 := (QuotientGroup.eq_one_iff _).mp (by
      change f ((a^n)⁻¹*z)=1
      rw [map_mul,map_inv,map_zpow,hn,inv_mul_cancel])
    have zEq : z = a^n*t := by dsimp [t]; group
    have tc : φ t ∈ Subgroup.center (G ⧸ S) := by
      exact (Subgroup.map_center_le_center onto) (Subgroup.mem_map_of_mem φ
        (ls4_center_of_class5 nil ht))
    rw [zEq,map_mul,map_zpow]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ ac _) tc
  have b : LS (G ⧸ S) 4 = ⊥ := by
    apply Subgroup.lowerCentralSeries_succ_eq_bot ⊤
    change LS (G ⧸ S) 3 ≤ Subgroup.center (G ⧸ S)
    exact (congrArg (fun T : Subgroup (G ⧸ S) => T ≤ Subgroup.center (G ⧸ S)) (map_ls φ onto 3)).mp all
  have m := map_ls φ onto 4
  rw [b,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at m
  exact le_antisymm m hS

end HaarP3LayerGen

#print axioms HaarP3LayerGen.ls4_eq_two_closure
