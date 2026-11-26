import HaarAbelianThirdAllFrontier
import HaarThirdAbelianRankOne
import HaarClass5Odd

namespace HaarAbelianThirdAllOdd
open HaarUniversal36 HaarAllNoncommuting HaarClass4Generate HaarAbelianThirdOdd
variable {G : Type*} [Group G]

theorem normalized (nil : ∃ d, L G d=⊥) (ab : AbelianThird G)
    (odd : Odd (Nat.card G))
    (x y : G) (hx : x≠1) (hy : y≠1) (hxy : x≠y) :
    ∃ e : ℕ, 2≤e ∧ e≤6 ∧ HasCycle x y (2^e) := by
  let S := Subgroup.closure ({x,y} : Set G)
  let X : S := ⟨x,Subgroup.subset_closure (by simp)⟩
  let Y : S := ⟨y,Subgroup.subset_closure (by simp)⟩
  have gen : Generates X Y := by
    apply Subgroup.map_subtype_inj.mp
    rw [MonoidHom.map_closure,Set.image_pair,Subgroup.map_top,Subgroup.subtype_range]
    rfl
  have mono (n : ℕ) : (L S n).map S.subtype ≤ L G n := by
    rw [Subgroup.top_subtype_lowerCentralSeries]
    exact Subgroup.lowerCentralSeries_mono n (show S≤⊤ from le_top)
  have cls : ∃ n, L S n=⊥ := by
    obtain ⟨n,hn⟩ := nil
    refine ⟨n,?_⟩
    apply Subgroup.map_subtype_inj.mp
    rw [Subgroup.map_bot]
    exact le_bot_iff.mp ((mono n).trans (le_of_eq hn))
  have abS : AbelianThird S := by
    intro a b ha hb
    exact Subtype.ext (ab a.val b.val ((mono 2) (Subgroup.mem_map_of_mem S.subtype ha))
      ((mono 2) (Subgroup.mem_map_of_mem S.subtype hb))).eq
  have hxS : X≠1 := fun e => hx (congrArg Subtype.val e)
  have hyS : Y≠1 := fun e => hy (congrArg Subtype.val e)
  have hxyS : X≠Y := fun e => hxy (congrArg Subtype.val e)
  have oddS : Odd (Nat.card S) := Odd.of_dvd_nat odd S.card_subgroup_dvd_card
  have lift (n : ℕ) : HasCycle X Y n → HasCycle x y n :=
    HaarClassFourFinite.mapped_cycle S.subtype Subtype.val_injective X Y
  by_cases c : L S 3=⊥
  · have c5 : L S 5=⊥ := le_bot_iff.mp
      ((Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup S) (by decide : 3≤5)).trans (le_of_eq c))
    obtain ⟨e,lo,hi,cy⟩ := HaarClass5Odd.normalized c5 oddS X Y hxS hyS hxyS
    exact ⟨e,lo,hi,lift _ cy⟩
  · have C : HasCycle X Y 64 := by
      rcases HaarAbelianThirdAllFrontier.rank_result cls abS c oddS X Y gen with e | size
      · exact e
      · exact HaarThirdAbelianRankOne.cycle abS cls c X Y gen size
    exact ⟨6,by decide,by decide,lift 64 C⟩

theorem any_ports (nil : ∃ d, L G d=⊥) (ab : AbelianThird G)
    (odd : Odd (Nat.card G))
    (r s t : G) (hr : r≠s) (ht : r≠t) (hs : s≠t) :
    ∃ e : ℕ, 2≤e ∧ e≤6 ∧ HaarAnyPorts.HasPortCycle r s t (2^e) := by
  obtain ⟨a,b,c⟩ := HaarAnyPorts.as_three r s t hr ht hs
  obtain ⟨e,lo,hi,cy⟩ := normalized nil ab odd (s*r⁻¹) (t*r⁻¹) a b c
  exact ⟨e,lo,hi,HaarAnyPorts.map_cycle r s t cy⟩

end HaarAbelianThirdAllOdd
#print axioms HaarAbelianThirdAllOdd.any_ports
