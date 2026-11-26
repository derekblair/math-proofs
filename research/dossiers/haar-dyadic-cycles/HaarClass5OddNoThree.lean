import HaarClass5TemplateCycles
import HaarAnyPorts

namespace HaarClass5OddNoThree
open scoped commutatorElement
open HaarUniversal36 HaarAllNoncommuting HaarClass4Ports HaarClass4Generate
variable {G : Type*} [Group G]

theorem cube_one (h : ¬ 3 ∣ Nat.card G) (a : G) (ha : a^(3:ℕ)=1) : a=1 := by
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp (orderOf_dvd_iff_pow_eq_one.mpr ha) with h1 | h3
  · exact orderOf_eq_one_iff.mp h1
  · exact (h (by simpa only [h3] using orderOf_dvd_natCard a)).elim

theorem noncube (nil : L G 5=⊥) (exact5 : L G 4 ≠ ⊥)
    (not_three : ¬3∣Nat.card G) (x y : G) (gen : Generates x y) :
    let f := QuotientGroup.mk' (L G 3)
    ¬ ((portU (f x) (f y))^(3:ℕ)=1 ∧ (portV (f x) (f y))^(3:ℕ)=1) := by
  let S := L G 3
  let f := QuotientGroup.mk' S
  let X := f x
  let Y := f y
  change ¬ ((portU X Y)^(3:ℕ)=1 ∧ (portV X Y)^(3:ℕ)=1)
  rintro ⟨hu,hv⟩
  have n3 : ¬3∣Nat.card (G ⧸ S) := fun d => not_three (d.trans S.card_quotient_dvd_card)
  have eu : portU X Y=1 := cube_one n3 _ hu
  have ev : portV X Y=1 := cube_one n3 _ hv
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

theorem normalized (nil : L G 5=⊥) (odd : Odd (Nat.card G))
    (not_three : ¬3∣Nat.card G) (x y : G) (hx : x≠1) (hy : y≠1) (hxy : x≠y) :
    ∃ e : ℕ, 2≤e ∧ e≤6 ∧ HasCycle x y (2^e) := by
  let S := Subgroup.closure ({x,y} : Set G)
  let X : S := ⟨x,Subgroup.subset_closure (by simp)⟩
  let Y : S := ⟨y,Subgroup.subset_closure (by simp)⟩
  have gen : Generates X Y := by
    apply Subgroup.map_subtype_inj.mp
    rw [MonoidHom.map_closure,Set.image_pair,Subgroup.map_top,Subgroup.subtype_range]
    rfl
  have cls : L S 5=⊥ := by
    apply Subgroup.map_subtype_inj.mp
    rw [Subgroup.map_bot,Subgroup.top_subtype_lowerCentralSeries,← le_bot_iff]
    exact (Subgroup.lowerCentralSeries_mono 5 (show S≤⊤ from le_top)).trans (le_of_eq nil)
  have hxS : X≠1 := fun e => hx (congrArg Subtype.val e)
  have hyS : Y≠1 := fun e => hy (congrArg Subtype.val e)
  have hxyS : X≠Y := fun e => hxy (congrArg Subtype.val e)
  have oddS : Odd (Nat.card S) := Odd.of_dvd_nat odd S.card_subgroup_dvd_card
  have n3S : ¬3∣Nat.card S := fun e => not_three (e.trans S.card_subgroup_dvd_card)
  have lift (n : ℕ) : HasCycle X Y n → HasCycle x y n :=
    HaarClassFourFinite.mapped_cycle S.subtype Subtype.val_injective X Y
  by_cases c4 : L S 4 = ⊥
  · rcases HaarClassFourOdd.odd_class_four c4 X Y oddS hxS hyS hxyS with e|e|e|e
    · exact ⟨2,by decide,by decide,lift 4 e⟩
    · exact ⟨3,by decide,by decide,lift 8 e⟩
    · exact ⟨4,by decide,by decide,lift 16 e⟩
    · exact ⟨5,by decide,by decide,lift 32 e⟩
  · have e := HaarClass5TemplateCycles.no_cube_case cls oddS X Y (noncube cls c4 n3S X Y gen)
    exact ⟨6,by decide,by decide,lift 64 e⟩

/-- An arbitrary choice of three distinct ports, in odd group order prime to
three, forces a simple power-of-two cycle of length at most 64. -/
theorem any_ports (nil : L G 5=⊥) (odd : Odd (Nat.card G)) (not_three : ¬3∣Nat.card G)
    (r s t : G) (hr : r≠s) (ht : r≠t) (hs : s≠t) :
    ∃ e : ℕ, 2≤e ∧ e≤6 ∧ HaarAnyPorts.HasPortCycle r s t (2^e) := by
  obtain ⟨a,b,c⟩ := HaarAnyPorts.as_three r s t hr ht hs
  obtain ⟨e,el,eh,w⟩ := normalized nil odd not_three (s*r⁻¹) (t*r⁻¹) a b c
  exact ⟨e,el,eh,HaarAnyPorts.map_cycle r s t w⟩

end HaarClass5OddNoThree
#print axioms HaarClass5OddNoThree.any_ports
