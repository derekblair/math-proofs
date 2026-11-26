import HaarP3LayerGenQuot
import HaarClass5TemplateCycles

namespace HaarP3RankSplit
open HaarUniversal36 HaarClass5TemplateClosure HaarAllNoncommuting
open HaarClass4Ports HaarClass4Generate HaarClass5TemplateCycles
open HaarClass5DirectionCover HaarClass5DirTables
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem at_least_one_port_tail (nil : L G 5=⊥) (exact5 : L G 4≠⊥)
    (x y : G) (gen : Generates x y) :
    let f := QuotientGroup.mk' (L G 3)
    ¬ (portU (f x) (f y)=1 ∧ portV (f x) (f y)=1) := by
  let S := L G 3
  let f := QuotientGroup.mk' S
  let X := f x
  let Y := f y
  change ¬ (portU X Y=1 ∧ portV X Y=1)
  rintro ⟨eu,ev⟩
  have cx : Commute (portC X Y) X := commutatorElement_eq_one_iff_commute.mp eu
  have cy : Commute (portC X Y) Y := commutatorElement_eq_one_iff_commute.mp ev
  have g : Generates X Y := map_gen f (QuotientGroup.mk'_surjective S) gen
  have bot : L (G ⧸ S) 2=⊥ := c_center_class_two X Y _ g (ports_xy X Y) (gen_center X Y _ g cx cy)
  have M : (L G 2).map f = L (G ⧸ S) 2 := map_ls f (QuotientGroup.mk'_surjective S) 2
  rw [bot,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at M
  have eq : L G 2 = L G 3 := le_antisymm M
    ((Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G)) (by decide : 2 ≤ 3))
  have nxt : L G 3 = L G 4 := congrArg (fun T : Subgroup G => ⁅T,(⊤ : Subgroup G)⁆) eq
  have fin : L G 4 = L G 5 := congrArg (fun T : Subgroup G => ⁅T,(⊤ : Subgroup G)⁆) nxt
  exact exact5 (fin.trans nil)

theorem card_span (u v : G) (nz : v≠1) (cube : v^(3:ℕ)=1) (hv : u ∈ Subgroup.zpowers v) :
    Nat.card (Subgroup.closure ({u,v} : Set G))=3 := by
  have w : Subgroup.closure ({u,v} : Set G)=Subgroup.zpowers v := by
    apply le_antisymm
    · apply (Subgroup.closure_le _).mpr
      intro a ha
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha
      rcases ha with rfl|rfl
      · exact hv
      · exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_eq_closure]
      exact Subgroup.closure_mono (by simp)
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [w,Nat.card_zpowers,orderOf_eq_prime cube nz]

theorem rank_result (nil : L G 5=⊥) (exact5 : L G 4≠⊥)
    (odd : Odd (Nat.card G)) (x y : G) (gen : Generates x y) :
    HasCycle x y 64 ∨ Nat.card ((L G 2).map (QuotientGroup.mk' (L G 3)))=3 := by
  classical
  let S := L G 3
  let f := QuotientGroup.mk' S
  let X := f x
  let Y := f y
  let u := portU X Y
  let v := portV X Y
  have not_both : ¬ (u=1 ∧ v=1) := at_least_one_port_tail nil exact5 x y gen
  by_cases cube : u^(3:ℕ)=1 ∧ v^(3:ℕ)=1
  · by_cases hcy : HasCycle x y 64
    · exact Or.inl hcy
    right
    have nil3 : L (G ⧸ S) 3=⊥ := quote_nil 3
    have nc : portC X Y∉L (G ⧸ S) 2 := by
      intro hC
      have a := next hC X
      have b := next hC Y
      change u∈L (G ⧸ S) 3 at a
      change v∈L (G ⧸ S) 3 at b
      rw [nil3] at a b
      exact not_both ⟨Subgroup.mem_bot.mp a,Subgroup.mem_bot.mp b⟩
    have bad : ∃ j : Fin 4, rel u v (D0 j) := by
      by_contra! h
      exact hcy (template_cycle nil odd x y 0 nc h)
    have span := HaarP3LayerGen.ls2_mod_ls3 x y gen
    have eq : (L G 2).map f=Subgroup.closure ({u,v} : Set (G ⧸ S)) := span
    change Nat.card ((L G 2).map f)=3
    rw [eq]
    have go (nv : v≠1) (hv : u∈Subgroup.zpowers v) :
        Nat.card (Subgroup.closure ({u,v} : Set (G ⧸ S)))=3 := card_span u v nv cube.2 hv
    by_cases h : v=1
    · have nu : u≠1 := fun hu => not_both ⟨hu,h⟩
      rw [Set.pair_comm]
      exact card_span v u nu cube.1 (by rw [h]; exact Subgroup.one_mem _)
    · apply go h
      obtain ⟨j,e⟩ := bad
      fin_cases j
      · have s : v=1 := by simpa [rel,D0] using e
        exact (h s).elim
      · have s : u=1 := by simpa [rel,D0] using e
        rw [s]; exact Subgroup.one_mem _
      · have s : u*v=1 := by simpa [rel,D0] using e
        rw [eq_inv_of_mul_eq_one_left s]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
      · have s : u*v^(2:ℕ)=1 := by simpa [rel,D0,zpow_natCast] using e
        rw [eq_inv_of_mul_eq_one_left s]
        exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
  · exact Or.inl (no_cube_case nil odd x y cube)

end HaarP3RankSplit
#print axioms HaarP3RankSplit.rank_result
