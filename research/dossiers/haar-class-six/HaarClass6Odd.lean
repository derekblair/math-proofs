import HaarClass6Frontier
import HaarClass6RankOneActual
import HaarClass5Odd

namespace HaarClass6Odd
open scoped commutatorElement
open HaarUniversal36 HaarAllNoncommuting HaarClass4Ports HaarClass4Generate
variable {G : Type*} [Group G]

theorem normalized (nil : L G 6=⊥) (odd : Odd (Nat.card G))
    (x y : G) (hx : x≠1) (hy : y≠1) (hxy : x≠y) :
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
  have lift (n : ℕ) : HasCycle X Y n → HasCycle x y n :=
    HaarClassFourFinite.mapped_cycle S.subtype Subtype.val_injective X Y
  by_cases c5 : L S 5 = ⊥
  · obtain ⟨e,lo,hi,cycle⟩ := HaarClass5Odd.normalized c5 oddS X Y hxS hyS hxyS
    exact ⟨e,lo,hi,lift (2^e) cycle⟩
  · have cy : HasCycle X Y 64 := by
      rcases HaarClass6Frontier.rank_result cls c5 oddS X Y gen with e | size
      · exact e
      · have dp : L S 3≠⊥ := by
          intro e
          apply c5
          exact le_bot_iff.mp
            ((Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup S) (by decide : 3≤5)).trans (le_of_eq e))
        exact HaarClass6RankOneActual.cycle cls dp X Y gen size
    exact ⟨6,by decide,by decide,lift 64 cy⟩

/-- An arbitrary choice of three distinct ports, in a finite group of odd order,
forces a simple power-of-two cycle of length at most 64. -/
theorem any_ports (nil : L G 6=⊥) (odd : Odd (Nat.card G))
    (r s t : G) (hr : r≠s) (ht : r≠t) (hs : s≠t) :
    ∃ e : ℕ, 2≤e ∧ e≤6 ∧ HaarAnyPorts.HasPortCycle r s t (2^e) := by
  obtain ⟨a,b,c⟩ := HaarAnyPorts.as_three r s t hr ht hs
  obtain ⟨e,el,eh,w⟩ := normalized nil odd (s*r⁻¹) (t*r⁻¹) a b c
  exact ⟨e,el,eh,HaarAnyPorts.map_cycle r s t w⟩

end HaarClass6Odd
#print axioms HaarClass6Odd.any_ports
