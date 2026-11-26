import HaarClass4Generate

namespace Ribbon5GeneratorDrop
open HaarClass4Structure HaarClass4Generate HaarClass4Ports
variable {G : Type*} [Group G]
open scoped commutatorElement

theorem comm_if_projected_trivial (nil : LS G 5=⊥) (x y : G)
    (gen : Generates x y) (hc : portC x y∈LS G 2) : portC x y=1 := by
  let S := LS G 2
  let φ := QuotientGroup.mk' S
  have g := map_gen φ (QuotientGroup.mk'_surjective S) gen
  have r : Commute (φ x) (φ y) := by
    have C : φ (portC x y)=1 := (QuotientGroup.eq_one_iff _).mpr hc
    change φ x*φ y=φ y*φ x
    simpa only [map_mul,C,mul_one] using congrArg φ (ports_xy x y)
  let : IsMulCommutative (G ⧸ S) := gen_comm _ _ g r
  have zero : LS (G ⧸ S) 1=⊥ :=
    Subgroup.top_lowerCentralSeries_one.trans (commutator_eq_bot (G ⧸ S))
  have h := map_ls φ (QuotientGroup.mk'_surjective S) 1
  rw [zero,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at h
  have d : LS G 1=LS G 2 :=
    le_antisymm h ((Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G)) (by decide : 1≤2))
  let step : Subgroup G → Subgroup G := fun H => ⁅H,(⊤ : Subgroup G)⁆
  have d₂ : LS G 2=LS G 3 := congrArg step d
  have d₃ : LS G 3=LS G 4 := congrArg step d₂
  have d₄ : LS G 4=LS G 5 := congrArg step d₃
  have all := d.trans (d₂.trans (d₃.trans (d₄.trans nil)))
  have hC := layer_c x y
  rw [all,Subgroup.mem_bot] at hC
  exact hC

end Ribbon5GeneratorDrop
#print axioms Ribbon5GeneratorDrop.comm_if_projected_trivial
