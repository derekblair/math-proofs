import HaarClass6RankOneGraph
import HaarP3LayerGenBridge

namespace HaarClass6RankOneActual
open scoped commutatorElement
open HaarUniversal36 HaarClass4Structure HaarClass4Ports HaarClass4Generate
open HaarP3LayerGen HaarAllNoncommuting
variable {G : Type*} [Group G]

theorem cycle (nil6 : L G 6=⊥) (deepG : L G 3≠⊥)
    (x y : G) (gen : Generates x y)
    (size : Nat.card ((L G 2).map (QuotientGroup.mk' (L G 3)))=3) :
    HasCycle x y 64 := by
  let N := L G 4
  let H := G ⧸ N
  let f := QuotientGroup.mk' N
  let g := QuotientGroup.mk' (L G 3)
  let S := (L G 2).map g
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have cyc : IsCyclic S := isCyclic_of_prime_card size
  obtain ⟨z,hz⟩ := (S.isCyclic_iff_exists_zpowers_eq_top).mp cyc
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (L G 3) z
  have onto := QuotientGroup.mk'_surjective N
  have map3 : (L G 3).map f=L H 3 := map_ls f onto 3
  have deep : L H 3≠⊥ := by
    intro h
    have z := map3
    rw [h,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at z
    have e := le_antisymm z (Subgroup.lowerCentralSeries_antitone _ (by decide : 3≤4))
    have e' : L G 4 = L G 5 := congrArg (fun T : Subgroup G => ⁅T,(⊤ : Subgroup G)⁆) e
    have e'' : L G 5 = L G 6 := congrArg (fun T : Subgroup G => ⁅T,(⊤ : Subgroup G)⁆) e'
    exact deepG (e.trans (e'.trans (e''.trans nil6)))
  exact HaarClass6RankOneGraph.all_models nil6 u hz.symm f (ls4quot_class4 G) deep x y
    (map_gen f onto gen) (ls2_map_card_in_ls4quot.trans size)

end HaarClass6RankOneActual
#print axioms HaarClass6RankOneActual.cycle
