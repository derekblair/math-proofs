import HaarClass6RankTwoGraph
import HaarP3LayerGenBridge
import HaarClass4Map

namespace HaarClass6RankTwoActual
open scoped commutatorElement
open HaarUniversal36 HaarClass4Structure HaarClass4Ports HaarClass4Generate
open HaarClass4Map HaarP3LayerGen HaarAllNoncommuting
variable {G : Type*} [Group G]

theorem cycle (nil6 : L G 6=⊥) (exact6 : L G 5≠⊥)
    (x y : G) (gen : Generates x y)
    (cu : (QuotientGroup.mk' (L G 3) (portU x y))^(3:ℕ)=1)
    (rank2 : ∀ u v : ℤ,
      (QuotientGroup.mk' (L G 3) (portU x y))^u *
        (QuotientGroup.mk' (L G 3) (portV x y))^v = 1 →
      u%3=0 ∧ v%3=0) : HasCycle x y 64 := by
  let N := L G 4
  let H := G ⧸ N
  let f := QuotientGroup.mk' N
  let X := f x
  let Y := f y
  let g := QuotientGroup.mk' (L G 3)
  have n3 : N ≤ (L G 3).comap (MonoidHom.id G) :=
    Subgroup.lowerCentralSeries_antitone _ (by decide : 3≤4)
  let q := QuotientGroup.map N (L G 3) (MonoidHom.id G) n3
  have eq (z : G) : q (f z)=g z := rfl
  let M := make (ls4quot_class4 G) X Y
  have onto := QuotientGroup.mk'_surjective N
  have genH := map_gen f onto gen
  have map3 : (L G 3).map f=L H 3 := map_ls f onto 3
  have deep : L H 3≠⊥ := by
    intro h
    have z := map3
    rw [h,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at z
    have e := le_antisymm z (Subgroup.lowerCentralSeries_antitone _ (by decide : 3≤4))
    have e' : L G 4 = L G 5 := congrArg (fun T : Subgroup G => ⁅T,(⊤ : Subgroup G)⁆) e
    have e'' : L G 5 = L G 6 := congrArg (fun T : Subgroup G => ⁅T,(⊤ : Subgroup G)⁆) e'
    exact exact6 (e''.trans nil6)
  have qkill {a : H} (ha : a∈L H 3) : q a=1 := by
    rw [←map3] at ha
    obtain ⟨w,hw,rfl⟩ := ha
    rw [eq]
    exact (QuotientGroup.eq_one_iff _).mpr hw
  have htail := tail_layers (ls4quot_class4 G) X Y
  have fU : f (portU x y)=portU X Y := map_portU f x y
  have fV : f (portV x y)=portV X Y := map_portV f x y
  have qU : q (portU X Y)=g (portU x y) := by rw [← fU,eq]
  have qV : q (portV X Y)=g (portV x y) := by rw [← fV,eq]
  have indep : ∀ u v : ℤ, (q (portU X Y))^u*(q (portV X Y))^v=1 →
      u%3=0 ∧ v%3=0 := by
    intro a b h
    rw [qU,qV] at h
    exact rank2 a b h
  let φ := QuotientGroup.mk' (L H 3)
  have Uc : (φ (portU X Y))^(3:ℕ)=1 := by
    have h : (portU x y)^(3:ℕ)∈L G 3 :=
      (QuotientGroup.eq_one_iff _).mp (by
        change g ((portU x y)^(3:ℕ))=1
        rw [map_pow]; exact cu)
    have t : f ((portU x y)^(3:ℕ))∈L H 3 := map3 ▸ Subgroup.mem_map_of_mem f h
    rw [map_pow,fU] at t
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr t
  have neU : φ (portU X Y)≠1 := by
    intro e
    have h : q (portU X Y)=1 := qkill ((QuotientGroup.eq_one_iff _).mp e)
    have c := indep 1 0 (by rw [h,one_zpow,zpow_zero,mul_one])
    norm_num at c
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have ou : orderOf (φ (portU X Y))=3 := orderOf_eq_prime Uc neU
  have oc := HaarP3Class4Order.c_order3 (portC X Y) X (layer_c X Y) ou
  exact HaarClass6RankTwoGraph.rank_two nil6 f (ls4quot_class4 G) deep x y genH q
    oc (qkill htail.1) (qkill htail.2.1) (qkill htail.2.2) indep

end HaarClass6RankTwoActual
#print axioms HaarClass6RankTwoActual.cycle
