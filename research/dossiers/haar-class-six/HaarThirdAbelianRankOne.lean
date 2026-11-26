import HaarThirdAbelianRankOneGraph
import HaarP3LayerGenBridge

namespace HaarThirdAbelianRankOne
open scoped commutatorElement
open HaarUniversal36 HaarClass4Structure HaarClass4Ports HaarClass4Generate
open HaarP3LayerGen HaarAllNoncommuting
variable {G : Type*} [Group G]

theorem cycle (ab : ∀ a b, a∈L G 2 → b∈L G 2 → Commute a b)
    (nil : ∃ n, L G n=⊥) (deepG : L G 3≠⊥)
    (x y : G) (gen : Generates x y)
    (size : Nat.card ((L G 2).map (QuotientGroup.mk' (L G 3)))=3) :
    HasCycle x y 64 := by
  let N := L G 4
  let H := G ⧸ N
  let f := QuotientGroup.mk' N
  have onto := QuotientGroup.mk'_surjective N
  have map3 : (L G 3).map f=L H 3 := map_ls f onto 3
  have deep : L H 3≠⊥ := by
    intro h
    have z := map3
    rw [h,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at z
    have e := le_antisymm z (Subgroup.lowerCentralSeries_antitone _ (by decide : 3≤4))
    have stable : ∀ k : ℕ, L G 3 = L G (3+k) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        exact e.trans (congrArg (fun T : Subgroup G => ⁅T,(⊤ : Subgroup G)⁆) ih)
    obtain ⟨n,hn⟩ := nil
    apply deepG
    rw [stable n]
    exact le_bot_iff.mp ((Subgroup.lowerCentralSeries_antitone _
      (by omega : n≤3+n)).trans (le_of_eq hn))
  exact HaarThirdAbelianRankOneGraph.all_models ab f (ls4quot_class4 G) deep x y
    (map_gen f onto gen) (ls2_map_card_in_ls4quot.trans size)

end HaarThirdAbelianRankOne
#print axioms HaarThirdAbelianRankOne.cycle
