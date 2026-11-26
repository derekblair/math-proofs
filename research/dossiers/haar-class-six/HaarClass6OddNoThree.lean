import HaarClass6ParallelCycle
import HaarClass5Odd

namespace HaarClass6OddNoThree
open HaarUniversal36 HaarClass4Ports HaarClass4Generate HaarAllNoncommuting
open HaarClass5TemplateClosure HaarClass6ParallelCycle
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem swap_cycle (x y : G) {n : ℕ} (h : HasCycle y x n) : HasCycle x y n := by
  obtain ⟨v,hv,e⟩ := h
  exact ⟨v,hv,fun j => by simpa only [HaarCycle.haarAdj,or_comm,or_left_comm] using e j⟩

theorem v_swapped (nil : L G 3=⊥) (x y : G) : portV y x=(portU x y)⁻¹ := by
  let c := portC x y
  let u := portU x y
  change ⁅portC y x,x⁆=u⁻¹
  rw [HaarClassFourFinite.swap_c,commutatorElement_inv_left,←commutatorElement_inv]
  change c⁻¹*u⁻¹*c=u⁻¹
  rw [((central_2 nil (layer_u x y) c).symm.inv_left.inv_right).eq,mul_assoc,inv_mul_cancel,mul_one]

theorem one_noncube (nil : L G 6=⊥) (deep : L G 5≠⊥) (n3 : ¬3∣Nat.card G)
    (x y : G) (gen : Generates x y) :
    let f := QuotientGroup.mk' (L G 3)
    ¬ ((portU (f x) (f y))^(3:ℕ)=1 ∧ (portV (f x) (f y))^(3:ℕ)=1) := by
  let S := L G 3
  let f := QuotientGroup.mk' S
  let X := f x
  let Y := f y
  change ¬ ((portU X Y)^(3:ℕ)=1 ∧ (portV X Y)^(3:ℕ)=1)
  rintro ⟨hu,hv⟩
  have nQ : ¬3∣Nat.card (G ⧸ S) := fun d => n3 (d.trans S.card_quotient_dvd_card)
  have eu := HaarClass5OddNoThree.cube_one nQ _ hu
  have ev := HaarClass5OddNoThree.cube_one nQ _ hv
  have cx : Commute (portC X Y) X := commutatorElement_eq_one_iff_commute.mp eu
  have cy : Commute (portC X Y) Y := commutatorElement_eq_one_iff_commute.mp ev
  have g : Generates X Y := map_gen f (QuotientGroup.mk'_surjective S) gen
  have bot : L (G ⧸ S) 2=⊥ := c_center_class_two X Y _ g (ports_xy X Y) (gen_center X Y _ g cx cy)
  have M : (L G 2).map f = L (G ⧸ S) 2 := map_ls f (QuotientGroup.mk'_surjective S) 2
  rw [bot,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at M
  have same : L G 2=L G 3 := le_antisymm M
    (Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G) (by decide : 2≤3))
  have next' (a b : ℕ) (h : L G a=L G b) : L G (a+1)=L G (b+1) :=
    congrArg (fun T : Subgroup G => ⁅T,(⊤ : Subgroup G)⁆) h
  exact deep ((next' 4 5 (next' 3 4 (next' 2 3 same))).trans nil)

theorem generated (nil : L G 6=⊥) (deep : L G 5≠⊥) (odd : Odd (Nat.card G))
    (n3 : ¬3∣Nat.card G) (x y : G) (gen : Generates x y) : HasCycle x y 64 := by
  let f := QuotientGroup.mk' (L G 3)
  have at_least := one_noncube nil deep n3 x y gen
  by_cases nv : (portV (f x) (f y))^(3:ℕ)=1
  · apply swap_cycle
    apply case_v nil odd y x
    change (portV (f y) (f x))^(3:ℕ)≠1
    simp only [v_swapped (quote_nil 3),inv_pow,ne_eq,inv_eq_one]
    exact fun u => at_least ⟨u,nv⟩
  · exact case_v nil odd x y nv

theorem normalized (nil : L G 6=⊥) (odd : Odd (Nat.card G))
    (not_three : ¬3∣Nat.card G) (x y : G) (hx : x≠1) (hy : y≠1) (hxy : x≠y) :
    ∃ e : ℕ, 2≤e ∧ e≤6 ∧ HasCycle x y (2^e) := by
  let S := Subgroup.closure ({x,y} : Set G)
  let X : S := ⟨x,Subgroup.subset_closure (by simp)⟩
  let Y : S := ⟨y,Subgroup.subset_closure (by simp)⟩
  have gen : Generates X Y := by
    apply Subgroup.map_subtype_inj.mp
    rw [MonoidHom.map_closure,Set.image_pair,Subgroup.map_top,Subgroup.subtype_range]
    rfl
  have cls : L S 6=⊥ := by
    apply Subgroup.map_subtype_inj.mp
    rw [Subgroup.map_bot,Subgroup.top_subtype_lowerCentralSeries,← le_bot_iff]
    exact (Subgroup.lowerCentralSeries_mono 6 (show S≤⊤ from le_top)).trans (le_of_eq nil)
  have hxS : X≠1 := fun e => hx (congrArg Subtype.val e)
  have hyS : Y≠1 := fun e => hy (congrArg Subtype.val e)
  have hxyS : X≠Y := fun e => hxy (congrArg Subtype.val e)
  have oddS : Odd (Nat.card S) := Odd.of_dvd_nat odd S.card_subgroup_dvd_card
  have n3S : ¬3∣Nat.card S := fun e => not_three (e.trans S.card_subgroup_dvd_card)
  have lift (n : ℕ) : HasCycle X Y n → HasCycle x y n :=
    HaarClassFourFinite.mapped_cycle S.subtype Subtype.val_injective X Y
  by_cases c5 : L S 5 = ⊥
  · obtain ⟨e,lo,hi,cycle⟩ := HaarClass5Odd.normalized c5 oddS X Y hxS hyS hxyS
    exact ⟨e,lo,hi,lift (2^e) cycle⟩
  · exact ⟨6,by decide,by decide,lift 64 (generated cls c5 oddS n3S X Y gen)⟩

/-- An arbitrary choice of three distinct ports, in odd group order prime to
three, forces a simple power-of-two cycle of length at most 64. -/
theorem any_ports (nil : L G 6=⊥) (odd : Odd (Nat.card G)) (not_three : ¬3∣Nat.card G)
    (r s t : G) (hr : r≠s) (ht : r≠t) (hs : s≠t) :
    ∃ e : ℕ, 2≤e ∧ e≤6 ∧ HaarAnyPorts.HasPortCycle r s t (2^e) := by
  obtain ⟨a,b,c⟩ := HaarAnyPorts.as_three r s t hr ht hs
  obtain ⟨e,el,eh,w⟩ := normalized nil odd not_three (s*r⁻¹) (t*r⁻¹) a b c
  exact ⟨e,el,eh,HaarAnyPorts.map_cycle r s t w⟩

end HaarClass6OddNoThree
#print axioms HaarClass6OddNoThree.any_ports
