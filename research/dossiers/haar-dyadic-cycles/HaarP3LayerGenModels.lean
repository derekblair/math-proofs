import HaarP3LayerGenPivot
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

namespace HaarP3LayerGen
open HaarClass4Structure HaarClass4Ports HaarClass4Generate

variable {G : Type*} [Group G]

theorem pow3_eq_one_of_card3 (S : Subgroup G) (h : Nat.card S=3)
    {g : G} (hg : g∈S) : g^3=1 :=
  orderOf_dvd_iff_pow_eq_one.mp (h ▸ S.orderOf_dvd_natCard hg)

theorem exists_pow3_of_order3 {a b : G} (ha : orderOf a = 3)
    (hb : b ∈ Subgroup.zpowers a) : ∃ n : Fin 3, a^n.val=b := by
  classical
  have ht : IsOfFinOrder a :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨3,by decide,by simpa only [ha] using pow_orderOf_eq_one a⟩
  have bmem := (ht.mem_zpowers_iff_mem_range_orderOf).mp hb
  rw [ha,Finset.mem_image] at bmem
  obtain ⟨n,hn,eq⟩ := bmem
  exact ⟨⟨n,Finset.mem_range.mp hn⟩,eq⟩

theorem pow_rep_of_card3 (S : Subgroup G) (h : Nat.card S=3)
    {g z : G} (hg : g∈S) (hz : z∈S) (h1 : g≠1) :
    ∃ n : Fin 3, g^n.val = z := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hg' : (⟨g,hg⟩ : S) ≠ 1 := by
    intro t
    exact h1 (congrArg Subtype.val t)
  have hgen : (⟨z,hz⟩ : S) ∈ Subgroup.zpowers (⟨g,hg⟩ : S) :=
    mem_zpowers_of_prime_card h hg'
  have horder : orderOf (⟨g,hg⟩ : S) = 3 :=
    orderOf_eq_prime (show (⟨g,hg⟩ : S)^3=1 from Subtype.ext (pow3_eq_one_of_card3 S h hg)) hg'
  obtain ⟨n,eq⟩ := exists_pow3_of_order3 horder hgen
  exact ⟨n,congrArg Subtype.val eq⟩

theorem layer_order_and_powers (S : Subgroup G) {g : G}
    (hS : S=Subgroup.zpowers g) (hne : S≠⊥) (hc : g^3=1) :
    orderOf g=3 ∧ Nat.card S=3 ∧ ∀ z∈S, ∃ n : Fin 3, z=g^n.val := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h1 : g≠1 := by
    intro e
    exact hne (hS.trans (Subgroup.zpowers_eq_bot.mpr e))
  have ho : orderOf g=3 := orderOf_eq_prime hc h1
  refine ⟨ho,by rw [hS,Nat.card_zpowers,ho],?_⟩
  intro z hz
  rw [hS] at hz
  obtain ⟨n,eq⟩ := exists_pow3_of_order3 ho hz
  exact ⟨n,eq.symm⟩

theorem spanU (h : LS G 4=⊥) (x y : G) (gen : Generates x y) (j : ℕ)
    (hb : (make h x y).b=(make h x y).a^j)
    (hd : (make h x y).d=(make h x y).a^(j*j)) :
    LS G 3=Subgroup.zpowers (make h x y).a := by
  rw [ls3_eq_tail_closure h x y gen]
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact Subgroup.mem_zpowers _
    · rw [hb]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    · rw [hd]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · rw [Subgroup.zpowers_eq_closure]
    exact Subgroup.closure_mono (by simp)

theorem spanV (h : LS G 4=⊥) (x y : G) (gen : Generates x y)
    (ha : (make h x y).a=1) (hb : (make h x y).b=1) :
    LS G 3=Subgroup.zpowers (make h x y).d := by
  rw [ls3_eq_tail_closure h x y gen]
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · rw [ha]; exact Subgroup.one_mem _
    · rw [hb]; exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_eq_closure]
    exact Subgroup.closure_mono (by simp)

theorem models (h : LS G 4=⊥) (deep : LS G 3≠⊥) (x y : G) (gen : Generates x y)
    (size : Nat.card ((LS G 2).map (QuotientGroup.mk' (LS G 3)))=3) :
    let E := make h x y
    Nat.card (LS G 3)=3 ∧
    ((∃ j t e : Fin 3, orderOf E.a=3 ∧ E.v=E.u^j.val*E.a^t.val ∧
      E.u^3=E.a^e.val ∧ E.b=E.a^j.val ∧ E.d=E.a^(j.val*j.val)) ∨
    (∃ t e : Fin 3, orderOf E.d=3 ∧ E.u=E.d^t.val ∧
      E.v^3=E.d^e.val ∧ E.a=1 ∧ E.b=1)) := by
  let E := make h x y
  let φ := QuotientGroup.mk' (LS G 3)
  let S := (LS G 2).map φ
  change Nat.card S=3 at size
  have uM : φ E.u ∈ S := Subgroup.mem_map_of_mem φ (layer_u x y)
  have vM : φ E.v ∈ S := Subgroup.mem_map_of_mem φ (layer_v x y)
  have uc : E.u^3 ∈ LS G 3 := (QuotientGroup.eq_one_iff _).mp (by
    change φ (E.u^3)=1
    rw [map_pow]
    exact pow3_eq_one_of_card3 S size uM)
  have vc : E.v^3 ∈ LS G 3 := (QuotientGroup.eq_one_iff _).mp (by
    change φ (E.v^3)=1
    rw [map_pow]
    exact pow3_eq_one_of_card3 S size vM)
  by_cases hU : φ E.u=1
  · have uB : E.u∈LS G 3 := (QuotientGroup.eq_one_iff _).mp hU
    obtain ⟨hc,ha,hb⟩ := pivotV h x y vc uB
    have ⟨ho,hcard,powers⟩ := layer_order_and_powers (LS G 3) (spanV h x y gen ha hb) deep hc
    obtain ⟨t,ht⟩ := powers E.u uB
    obtain ⟨e,he⟩ := powers (E.v^3) vc
    exact ⟨hcard,Or.inr ⟨t,e,ho,ht,he,ha,hb⟩⟩
  · obtain ⟨j,hj⟩ := pow_rep_of_card3 S size uM vM hU
    let T := (E.u^j.val)⁻¹*E.v
    have hT : T∈LS G 3 := (QuotientGroup.eq_one_iff _).mp (by
      change φ ((E.u^j.val)⁻¹*E.v)=1
      rw [map_mul,map_inv,map_pow,hj,inv_mul_cancel])
    have rel : E.v=E.u^j.val*T := by dsimp [T]; group
    obtain ⟨hc,hb,hd⟩ := pivotU h x y j.val uc T hT rel
    have ⟨ho,hcard,powers⟩ := layer_order_and_powers (LS G 3) (spanU h x y gen j.val hb hd) deep hc
    obtain ⟨t,ht⟩ := powers T hT
    obtain ⟨e,he⟩ := powers (E.u^3) uc
    exact ⟨hcard,Or.inl ⟨j,t,e,ho,rel.trans (congrArg _ ht),he,hb,hd⟩⟩

end HaarP3LayerGen

#print axioms HaarP3LayerGen.models
