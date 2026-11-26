import HaarClass5OddNoThree
import HaarP3FifthDispatch
import HaarP3RankSplit

namespace HaarClass5Odd
open scoped commutatorElement
open HaarUniversal36 HaarAllNoncommuting HaarClass4Ports HaarClass4Generate
variable {G : Type*} [Group G]

theorem normalized (nil : L G 5=⊥) (odd : Odd (Nat.card G))
    (x y : G) (hx : x≠1) (hy : y≠1) (hxy : x≠y) :
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
  have lift (n : ℕ) : HasCycle X Y n → HasCycle x y n :=
    HaarClassFourFinite.mapped_cycle S.subtype Subtype.val_injective X Y
  by_cases c4 : L S 4 = ⊥
  · rcases HaarClassFourOdd.odd_class_four c4 X Y oddS hxS hyS hxyS with e|e|e|e
    · exact ⟨2,by decide,by decide,lift 4 e⟩
    · exact ⟨3,by decide,by decide,lift 8 e⟩
    · exact ⟨4,by decide,by decide,lift 16 e⟩
    · exact ⟨5,by decide,by decide,lift 32 e⟩
  · have cycle : HasCycle X Y 32 ∨ HasCycle X Y 64 := by
      rcases HaarP3RankSplit.rank_result cls c4 oddS X Y gen with e | size
      · exact Or.inr e
      rcases HaarP3Class4Dispatch.dispatch cls c4 X Y gen size with e | exc
      · exact Or.inr e
      exact HaarP3FifthDispatch.dispatch cls c4 X Y gen exc
    rcases cycle with e | e
    · exact ⟨5,by decide,by decide,lift 32 e⟩
    · exact ⟨6,by decide,by decide,lift 64 e⟩

/-- An arbitrary choice of three distinct ports, in a finite group of odd order,
forces a simple power-of-two cycle of length at most 64. -/
theorem any_ports (nil : L G 5=⊥) (odd : Odd (Nat.card G))
    (r s t : G) (hr : r≠s) (ht : r≠t) (hs : s≠t) :
    ∃ e : ℕ, 2≤e ∧ e≤6 ∧ HaarAnyPorts.HasPortCycle r s t (2^e) := by
  obtain ⟨a,b,c⟩ := HaarAnyPorts.as_three r s t hr ht hs
  obtain ⟨e,el,eh,w⟩ := normalized nil odd (s*r⁻¹) (t*r⁻¹) a b c
  exact ⟨e,el,eh,HaarAnyPorts.map_cycle r s t w⟩

end HaarClass5Odd
#print axioms HaarClass5Odd.any_ports
