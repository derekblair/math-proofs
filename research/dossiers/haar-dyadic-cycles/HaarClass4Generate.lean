import HaarClass4Ports

namespace HaarClass4Generate

open scoped commutatorElement
open HaarClass4Structure HaarClass4Ports

variable {G H : Type*} [Group G] [Group H]

def Generates (x y : G) : Prop := Subgroup.closure ({x,y} : Set G) = ⊤

theorem map_gen (φ : G →* H) (onto : Function.Surjective φ) {x y : G}
    (h : Generates x y) : Generates (φ x) (φ y) := by
  unfold Generates at h ⊢
  rw [← Set.image_pair,← MonoidHom.map_closure,h,Subgroup.map_top,MonoidHom.range_eq_top.mpr onto]

theorem gen_comm (x y : G) (h : Generates x y) (c : Commute x y) :
    IsMulCommutative G := by
  have pair : ({x,y} : Set G).Pairwise Commute := by
    intro a ha b hb _
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Commute.refl _
    · exact c
    · exact c.symm
    · exact Commute.refl _
  have Z := Subgroup.isMulCommutative_closure pair
  change Subgroup.closure ({x,y} : Set G) = ⊤ at h
  rw [h] at Z
  rw [isMulCommutative_iff] at Z ⊢
  intro a b
  exact congrArg Subtype.val (Z ⟨a,Subgroup.mem_top a⟩ ⟨b,Subgroup.mem_top b⟩)

theorem gen_center (x y c : G) (h : Generates x y)
    (cx : Commute c x) (cy : Commute c y) : c ∈ Subgroup.center G := by
  have incl : Subgroup.closure ({x,y} : Set G) ≤ Subgroup.centralizer ({c} : Set G) := by
    apply (Subgroup.closure_le _).mpr
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr cx.symm.eq
    · exact Subgroup.mem_centralizer_singleton_iff.mpr cy.symm.eq
  rw [h] at incl
  exact Subgroup.mem_center_iff.mpr (fun z => (Subgroup.mem_centralizer_singleton_iff.mp
    (incl (Subgroup.mem_top z))))

theorem map_ls (φ : G →* H) (onto : Function.Surjective φ) (n : ℕ) :
    (LS G n).map φ = LS H n := by
  rw [Subgroup.map_lowerCentralSeries,Subgroup.map_top,MonoidHom.range_eq_top.mpr onto]

theorem c_center_class_two (x y c : G) (gen : Generates x y)
    (e : x*y=y*x*c) (hc : c∈Subgroup.center G) :
    LS G 2 = ⊥ := by
  let S := Subgroup.center G
  let φ := QuotientGroup.mk' S
  have sc : φ c=1 := (QuotientGroup.eq_one_iff c).mpr hc
  have comm : Commute (φ x) (φ y) := by
    change φ x*φ y=φ y*φ x
    simpa [sc] using congrArg φ e
  let : IsMulCommutative (G ⧸ S) :=
    gen_comm _ _ (map_gen φ (QuotientGroup.mk'_surjective S) gen) comm
  have cBot : LS (G ⧸ S) 1=⊥ := by
    exact Subgroup.top_lowerCentralSeries_one.trans (commutator_eq_bot (G ⧸ S))
  have m := map_ls φ (QuotientGroup.mk'_surjective S) 1
  rw [cBot,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at m
  exact Subgroup.lowerCentralSeries_succ_eq_bot ⊤ m

theorem deep_survives (x y : G) (gen : Generates x y)
    (h : LS G 4=⊥) (deep : LS G 3≠⊥) :
    portU x y ∉ LS G 3 ∨ portV x y ∉ LS G 3 := by
  by_contra! hn
  let S := LS G 3
  let φ := QuotientGroup.mk' S
  have cu : φ (portU x y)=1 := (QuotientGroup.eq_one_iff _).mpr hn.1
  have cv : φ (portV x y)=1 := (QuotientGroup.eq_one_iff _).mpr hn.2
  have cx : Commute (φ (portC x y)) (φ x) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa [portU,map_commutatorElement] using cu
  have cy : Commute (φ (portC x y)) (φ y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa [portV,map_commutatorElement] using cv
  have e : φ x*φ y=φ y*φ x*φ (portC x y) := by
    simpa using congrArg φ (ports_xy x y)
  have gen' := map_gen φ (QuotientGroup.mk'_surjective S) gen
  have zb := c_center_class_two (φ x) (φ y) (φ (portC x y)) gen' e (gen_center _ _ _ gen' cx cy)
  have map := map_ls φ (QuotientGroup.mk'_surjective S) 2
  rw [zb, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at map
  have le : LS G 3 ≤ LS G 2 := (Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G)) (by decide : 2 ≤ 3)
  have same : LS G 2 = LS G 3 := le_antisymm map le
  have e4 : LS G 3 = LS G 4 := congrArg (fun T : Subgroup G => ⁅T,(⊤ : Subgroup G)⁆) same
  exact deep (e4.trans h)

end HaarClass4Generate

#print axioms HaarClass4Generate.deep_survives
