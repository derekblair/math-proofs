import HaarThirdAbelianRankTwoGraph
import HaarP3LayerGenBridge
import HaarClass4Map

namespace HaarThirdAbelianRankTwo
open scoped commutatorElement
open HaarUniversal36 HaarClass4Structure HaarClass4Ports HaarClass4Generate
open HaarClass4Map HaarP3LayerGen HaarAllNoncommuting
variable {G : Type*} [Group G]

theorem strict_of_nil (nil : ∃ n, L G n=⊥) (deepG : L G 3≠⊥) :
    L G 3≠L G 4 := by
  intro e
  apply deepG
  obtain ⟨n,hn⟩ := nil
  by_cases small : n≤3
  · exact le_bot_iff.mp ((Subgroup.lowerCentralSeries_antitone _ small).trans hn.le)
  · have stable (i : ℕ) : L G (3+i)=L G 3 := by
      induction i with
      | zero => rfl
      | succ i ih =>
        change (⊤ : Subgroup G).lowerCentralSeries (3+i+1)=L G 3
        rw [Subgroup.lowerCentralSeries_succ]
        change ⁅L G (3+i),(⊤ : Subgroup G)⁆ = L G 3
        rw [ih]
        exact e.symm
    have he : 3+(n-3)=n := by omega
    have hdeep := stable (n-3)
    rw [he,hn] at hdeep
    exact hdeep.symm

theorem cycle_strict (strict : L G 3≠L G 4)
    (abel : ∀ a b : G, a ∈ L G 2 → b ∈ L G 2 → Commute a b)
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
    exact strict e
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
  exact HaarThirdAbelianRankTwoGraph.rank_two abel f (ls4quot_class4 G) deep x y genH q
    oc (qkill htail.1) (qkill htail.2.1) (qkill htail.2.2) indep

theorem cycle (nil : ∃ n, L G n=⊥) (deepG : L G 3≠⊥)
    (abel : ∀ a b : G, a ∈ L G 2 → b ∈ L G 2 → Commute a b)
    (x y : G) (gen : Generates x y)
    (cu : (QuotientGroup.mk' (L G 3) (portU x y))^(3:ℕ)=1)
    (rank2 : ∀ u v : ℤ,
      (QuotientGroup.mk' (L G 3) (portU x y))^u *
        (QuotientGroup.mk' (L G 3) (portV x y))^v = 1 →
      u%3=0 ∧ v%3=0) : HasCycle x y 64 :=
  cycle_strict (strict_of_nil nil deepG) abel x y gen cu rank2

end HaarThirdAbelianRankTwo
#print axioms HaarThirdAbelianRankTwo.cycle
#print axioms HaarThirdAbelianRankTwo.cycle_strict
