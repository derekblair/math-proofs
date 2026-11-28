import N63CrossCharge

namespace Erdos151H13
open Finset NineLinkPivot
open scoped BigOperators
set_option maxHeartbeats 100000
variable {V : Type*} [DecidableEq V]
variable (L : V → V → Prop) [DecidableRel L]

theorem four_link_degree_sum_le_eight
    (sym : ∀ {a b}, L a b → L b a) (irr : ∀ a, ¬L a a)
    (S : Finset V) (s4 : S.card=4)
    (tf : ∀ x ∈ S, ∀ a ∈ S, ∀ b ∈ S, L x a → L x b → ¬L a b) :
    (∑ x ∈ S, deg L S x) ≤ 8 := by
  by_cases cap : ∀ x ∈ S, deg L S x ≤ 2
  · calc
      _ ≤ ∑ x ∈ S, (2:ℕ) := Finset.sum_le_sum cap
      _ = 8 := by simp [s4]
  · push Not at cap
    obtain ⟨x,hx,hi⟩ := cap
    let K := near L S x
    have nx : x ∉ K := by simp [K,near,irr]
    have js : insert x K ⊆ S := insert_subset_iff.mpr ⟨hx,filter_subset _ _⟩
    have kc : (insert x K).card = K.card+1 := card_insert_of_notMem nx
    have kbound := card_le_card js
    have kd : deg L S x=3 := by
      change K.card=3
      change 2<K.card at hi
      omega
    have eqS : insert x K=S := eq_of_subset_of_card_le js (by
      rw [kc,s4]
      change K.card=3 at kd
      omega)
    have h := degree_sum L sym irr S tf x hx
    dsimp only at h
    change _ = 2*deg L S x + (∑ y ∈ S \ insert x K, (deg L S y + deg L K y)) at h
    simp [eqS,kd] at h
    omega

theorem charged_target_order_nine_deficit
    (sym : ∀ {a b}, L a b → L b a) (irr : ∀ a, ¬L a a)
    (S : Finset V) (s9 : S.card=9)
    (tf : ∀ x ∈ S, ∀ a ∈ S, ∀ b ∈ S, L x a → L x b → ¬L a b)
    (p : V) (hp : p ∈ S) (k4 : deg L S p = 4)
    (min2 : ∀ a ∈ S, 2 ≤ deg L S a)
    (cross : ∀ z ∈ S, z ≠ p → ¬L p z → deg L (near L S p) z ≤ 1) :
    (∑ x ∈ S, deg L S x) ≤ 24 := by
  obtain ⟨_,_,row,_⟩ := target_link_row_degree L sym irr S tf p hp k4 min2 cross
  let E := S \ insert p (near L S p)
  have hsub : insert p (near L S p) ⊆ S := insert_subset_iff.mpr ⟨hp,filter_subset _ _⟩
  have n : p ∉ near L S p := by simp [near,irr]
  have sz := card_sdiff_add_card_eq_card hsub
  rw [card_insert_of_notMem n] at sz
  change E.card+((near L S p).card+1) = S.card at sz
  change (near L S p).card=4 at k4
  have e4 : E.card=4 := by omega
  have etf : ∀ x ∈ E, ∀ a ∈ E, ∀ b ∈ E, L x a → L x b → ¬L a b :=
    fun x hx a ha b hb => tf x (mem_sdiff.mp hx).1 a (mem_sdiff.mp ha).1 b (mem_sdiff.mp hb).1
  have cap := four_link_degree_sum_le_eight L sym irr E e4 etf
  change _ ≤ 8+2*(S.card-5)+(∑ z ∈ E, deg L E z) at row
  omega

/-- The extremal five-vertex triangle-free link is necessarily K(3,2).
The witnesses are the degree-three pivot and its unique nonneighbor. -/
theorem five_link_degree_sum_le_twelve
    (sym : ∀ {a b}, L a b → L b a) (irr : ∀ a, ¬L a a)
    (S : Finset V) (s5 : S.card=5)
    (tf : ∀ x ∈ S, ∀ a ∈ S, ∀ b ∈ S, L x a → L x b → ¬L a b) :
    (∑ x ∈ S, deg L S x) ≤ 12 ∧
    ((∑ x ∈ S, deg L S x) = 12 →
      ∃ p ∈ S, ∃ q ∈ S, q ≠ p ∧ ¬L p q ∧
        (near L S p).card=3 ∧ near L S q=near L S p) := by
  by_cases cap : ∀ x ∈ S, deg L S x ≤ 2
  · have h : (∑ x ∈ S, deg L S x) ≤ 10 := calc
      _ ≤ ∑ x ∈ S, (2:ℕ) := Finset.sum_le_sum cap
      _ = 10 := by simp [s5]
    exact ⟨by omega,fun h12 => by omega⟩
  push Not at cap
  obtain ⟨p,hp,hi⟩ := cap
  let K := near L S p
  let E := S \ insert p K
  have pn : p ∉ K := by simp [K,near,irr]
  have ps : insert p K ⊆ S := insert_subset_iff.mpr ⟨hp,filter_subset _ _⟩
  have size := card_sdiff_add_card_eq_card ps
  change E.card+(insert p K).card=S.card at size
  rw [card_insert_of_notMem pn,s5] at size
  change 2<K.card at hi
  have eq := degree_sum L sym irr S tf p hp
  dsimp only at eq
  change _ = 2*K.card + (∑ q ∈ E, (deg L S q + deg L K q)) at eq
  by_cases h4 : K.card=4
  · have ee : E=∅ := card_eq_zero.mp (by omega)
    simp [ee,h4] at eq
    exact ⟨by omega,fun h12 => by omega⟩
  have k3 : K.card=3 := by omega
  have e1 : E.card=1 := by omega
  obtain ⟨q,hq⟩ := card_eq_one.mp e1
  have qE : q∈E := by simp [hq]
  obtain ⟨qs,qn⟩ := mem_sdiff.mp qE
  have qp : q≠p := fun zz => qn (mem_insert.mpr (Or.inl zz))
  have pq : ¬L p q := fun h => qn (mem_insert.mpr (Or.inr (mem_filter.mpr ⟨qs,h⟩)))
  have qK : near L S q ⊆ K := by
    intro z hz
    by_contra nk
    obtain ⟨zs,qz⟩ := mem_filter.mp hz
    have zp : z≠p := fun j => pq (sym (j ▸ qz))
    have zE : z∈E := mem_sdiff.mpr ⟨zs,fun j => (mem_insert.mp j).elim zp nk⟩
    have zq : z=q := by simpa [hq] using zE
    exact irr q (zq ▸ qz)
  have cut : near L S q = near L K q := by
    ext z
    constructor
    · intro zS
      exact mem_filter.mpr ⟨qK zS,(mem_filter.mp zS).2⟩
    · intro zK
      obtain ⟨zk,zz⟩ := mem_filter.mp zK
      exact mem_filter.mpr ⟨(mem_filter.mp zk).1,zz⟩
  simp only [hq,Finset.sum_singleton,k3] at eq
  have uq : (near L S q).card ≤ K.card := card_le_card qK
  change _ = 6 + ((near L S q).card + (near L K q).card) at eq
  rw [←cut] at eq
  refine ⟨by omega,fun total => ⟨p,hp,q,qs,qp,pq,k3,?_⟩⟩
  exact eq_of_subset_of_card_le qK (by change K.card ≤ (near L S q).card; omega)

/-- Equality at a ten-vertex charged target forces every exterior
vertex to have its unique cross edge, and its induced graph is K(3,2). -/
theorem charged_target_ten_equality
    (sym : ∀ {a b}, L a b → L b a) (irr : ∀ a, ¬L a a)
    (S : Finset V) (s10 : S.card=10)
    (tf : ∀ x ∈ S, ∀ a ∈ S, ∀ b ∈ S, L x a → L x b → ¬L a b)
    (p : V) (hp : p ∈ S) (k4 : deg L S p = 4)
    (min2 : ∀ a ∈ S, 2 ≤ deg L S a)
    (cross : ∀ z ∈ S, z ≠ p → ¬L p z → deg L (near L S p) z ≤ 1)
    (density : 30 ≤ ∑ x ∈ S, deg L S x) :
    let K := near L S p
    let E := S \ insert p K
    (∀ z ∈ E, deg L K z=1) ∧
    ∃ x ∈ E, ∃ y ∈ E, y ≠ x ∧ ¬L x y ∧
        (near L E x).card=3 ∧ near L E y=near L E x := by
  dsimp only
  let K := near L S p
  let E := S \ insert p K
  have sub : insert p K ⊆ S := insert_subset_iff.mpr ⟨hp,filter_subset _ _⟩
  have np : p ∉ K := by simp [K,near,irr]
  have sz := card_sdiff_add_card_eq_card sub
  change E.card+(insert p K).card=S.card at sz
  rw [card_insert_of_notMem np,s10] at sz
  change K.card=4 at k4
  have e5 : E.card=5 := by omega
  have etf : ∀ x ∈ E, ∀ a ∈ E, ∀ b ∈ E, L x a → L x b → ¬L a b :=
    fun x hx a ha b hb => tf x (mem_sdiff.mp hx).1 a (mem_sdiff.mp ha).1 b (mem_sdiff.mp hb).1
  obtain ⟨upper,model⟩ := five_link_degree_sum_le_twelve L sym irr E e5 etf
  obtain ⟨_,_,_,eq⟩ := target_link_row_degree L sym irr S tf p hp k4 min2 cross
  change _ = 8+2*(∑ z ∈ E, deg L K z)+(∑ z ∈ E, deg L E z) at eq
  have cap (z : V) (hz : z∈E) : deg L K z ≤ 1 := by
    obtain ⟨zs,ze⟩ := mem_sdiff.mp hz
    exact cross z zs (fun h => ze (mem_insert.mpr (Or.inl h)))
      (fun h => ze (mem_insert.mpr (Or.inr (mem_filter.mpr ⟨zs,h⟩))))
  have uc : (∑ z ∈ E, deg L K z) ≤ 5 := by
    simpa [e5] using (Finset.sum_le_sum (g:=fun _ => 1) (fun z hz => cap z hz))
  have ec : (∑ z ∈ E, deg L K z)=5 := by omega
  have ie : (∑ z ∈ E, deg L E z)=12 := by omega
  refine ⟨?_,model ie⟩
  intro z hz
  have cc : (∑ y ∈ E.erase z, deg L K y) ≤ (E.erase z).card := by
    simpa using (Finset.sum_le_sum (g:=fun _ => 1) (fun y hy => cap y (mem_of_mem_erase hy)))
  have sum := Finset.sum_erase_add E (fun y => deg L K y) hz
  have card : (E.erase z).card+1=E.card := card_erase_add_one hz
  have t := cap z hz
  change deg L K z=1
  omega

#print axioms charged_target_order_nine_deficit
#print axioms five_link_degree_sum_le_twelve
#print axioms charged_target_ten_equality
end Erdos151H13
