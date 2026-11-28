import N63SurplusPrice
import NineLinkPivot

namespace Erdos151H13
open Erdős151 Erdos151H12

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

def crossK (p v : V) : Finset V := neighbors C p ∩ neighbors C v

/-- For the four common core neighbors of a charging pivot, a remaining
neighbor of the target can meet at most one of the four, even in ambient G. -/
theorem actual_target_cross_at_most_one (p v z : V)
    (sub : ∀ a b, C a b → G a b)
    (newPrice : ∀ x ∈ crossK C p v,
        (neighbors G x∩neighbors G p).card = actualLinkDegree G C p x)
    (sharedPrice : ∀ x ∈ crossK C p v, ∀ y ∈ crossK C p v, x≠y →
        ((neighbors G x∩neighbors G y)\insert p (neighbors G p)).card=0)
    (zv : z ∈ neighbors C v) (nzp : z ≠ p) (nzK : z ∉ crossK C p v) :
    ((crossK C p v).filter fun x => G x z).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hxK,hxz⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyK,hyz⟩ := Finset.mem_filter.mp hy
  by_cases hpz : G p z
  · have hnc : ¬ C p z := fun e => nzK (Finset.mem_inter.mpr ⟨(mem_neighbors C).mpr e,zv⟩)
    exact False.elim ((no_new_center_attachments G C p x z sub (newPrice x hxK) hpz hnc) hxz)
  · by_contra hne
    exact (no_shared_exterior G p x y z (sharedPrice x hxK y hyK hne) nzp hpz hxz) hyz

theorem actual_target_core_cross_at_most_one (p v z : V)
    (sub : ∀ a b, C a b → G a b)
    (newPrice : ∀ x ∈ crossK C p v,
        (neighbors G x∩neighbors G p).card = actualLinkDegree G C p x)
    (sharedPrice : ∀ x ∈ crossK C p v, ∀ y ∈ crossK C p v, x≠y →
        ((neighbors G x∩neighbors G y)\insert p (neighbors G p)).card=0)
    (zv : z ∈ neighbors C v) (nzp : z ≠ p) (nzK : z ∉ crossK C p v) :
    ((crossK C p v).filter fun x => C x z).card ≤ 1 := by
  apply le_trans _ (actual_target_cross_at_most_one G C p v z sub newPrice sharedPrice zv nzp nzK)
  apply Finset.card_le_card
  intro a ha
  obtain ⟨ac,h⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨ac,sub _ _ h⟩

#print axioms actual_target_cross_at_most_one
#print axioms actual_target_core_cross_at_most_one
end Erdos151H13

namespace Erdos151H13
open Finset NineLinkPivot
open scoped BigOperators
variable {V : Type*} [DecidableEq V]
variable (L : V → V → Prop) [DecidableRel L]

/-- Counting the same cross edges from the two parts. -/
theorem cross_transpose (sym : ∀ {a b}, L a b → L b a) (K E : Finset V) :
    (∑ x ∈ K, deg L E x) = ∑ z ∈ E, deg L K z := by
  simp only [deg, near, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : L x z
  · simp [h,sym h]
  · simp [h,show ¬ L z x from fun hz => h (sym hz)]

theorem target_link_row_degree
    (sym : ∀ {a b}, L a b → L b a)
    (irr : ∀ a, ¬L a a)
    (S : Finset V)
    (tf : ∀ x ∈ S, ∀ a ∈ S, ∀ b ∈ S, L x a → L x b → ¬L a b)
    (p : V) (hp : p ∈ S) (k4 : deg L S p = 4)
    (min2 : ∀ a ∈ S, 2 ≤ deg L S a)
    (cross : ∀ z ∈ S, z ≠ p → ¬L p z → deg L (near L S p) z ≤ 1) :
    9 ≤ S.card ∧ (∀ a ∈ near L S p, deg L S a + 7 ≤ S.card) ∧
      ((∑ a ∈ S, deg L S a) ≤ 8+2*(S.card-5)+
        ∑ z ∈ S \ insert p (near L S p), deg L (S \ insert p (near L S p)) z) ∧
      ((∑ a ∈ S, deg L S a) = 8+2*(∑ z ∈ S \ insert p (near L S p), deg L (near L S p) z)+
        ∑ z ∈ S \ insert p (near L S p), deg L (S \ insert p (near L S p)) z) := by
  let K := near L S p
  let E := S \ insert p K
  have pK : p ∉ K := by simp [K,near,irr]
  have kS : K ⊆ S := filter_subset _ _
  have kpS : insert p K ⊆ S := insert_subset_iff.mpr ⟨hp,kS⟩
  have k4' : K.card=4 := k4
  have size := card_sdiff_add_card_eq_card kpS
  change E.card+(insert p K).card=S.card at size
  rw [card_insert_of_notMem pK,k4'] at size
  have spec (z : V) (hz : z ∈ E) : z ∈ S ∧ z≠p ∧ ¬L p z := by
    obtain ⟨hs,hn⟩ := mem_sdiff.mp hz
    exact ⟨hs,fun eq => hn (mem_insert.mpr (Or.inl eq)),
      fun e => hn (mem_insert.mpr (Or.inr (mem_filter.mpr ⟨hs,e⟩)))⟩
  have sumUpper : (∑ a ∈ K, deg L E a) ≤ E.card := by
    rw [cross_transpose L sym]
    simpa using (Finset.sum_le_sum (g:=fun _ => 1) (fun z hz =>
      cross z (spec z hz).1 (spec z hz).2.1 (spec z hz).2.2))
  have row (a : V) (ha : a ∈ K) : deg L S a = 1+deg L E a := by
    have pp := (mem_filter.mp ha).2
    have nf : near L S a = insert p (near L E a) := by
      ext z
      simp only [near,mem_filter,mem_insert,E,mem_sdiff]
      constructor
      · rintro ⟨zs,az⟩
        by_cases eq : z=p
        · exact Or.inl eq
        · refine Or.inr ⟨⟨zs,?_⟩,az⟩
          intro inside
          rcases inside with h|h
          · exact eq h
          · exact tf p hp a (kS ha) z zs pp (mem_filter.mp h).2 az
      · rintro (rfl|⟨⟨zs,_⟩,az⟩)
        · exact ⟨hp,sym pp⟩
        · exact ⟨zs,az⟩
    unfold deg
    rw [nf,card_insert_of_notMem]
    · omega
    · intro h
      exact (spec p (mem_filter.mp h).1).2.1 rfl
  have one (a : V) (ha : a ∈ K) : 1 ≤ deg L E a := by
    have h := row a ha
    have m := min2 a (kS ha)
    omega
  have lower : K.card ≤ ∑ a ∈ K, deg L E a := by
    simpa using (Finset.sum_le_sum (f:=fun _ => 1) (fun a ha => one a ha))
  have zrow (z : V) (hz : z ∈ E) : deg L S z = deg L K z + deg L E z := by
    have zz := spec z hz
    have ex : ¬L z p := fun h => zz.2.2 (sym h)
    have hu : near L S z = (near L K z) ∪ (near L E z) := by
      ext a
      simp only [near,mem_filter,mem_union,E,mem_sdiff]
      constructor
      · rintro ⟨as,za⟩
        by_cases ha : a∈K
        · exact Or.inl ⟨ha,za⟩
        · exact Or.inr ⟨⟨as,fun g => (mem_insert.mp g).elim (fun q => ex (q ▸ za)) ha⟩,za⟩
      · rintro (⟨ak,za⟩|⟨⟨as,_⟩,za⟩)
        · exact ⟨kS ak,za⟩
        · exact ⟨as,za⟩
    unfold deg
    rw [hu,card_union_of_disjoint]
    apply disjoint_left.mpr
    intro a ha hb
    exact (mem_sdiff.mp (mem_filter.mp hb).1).2
      (mem_insert.mpr (Or.inr (mem_filter.mp ha).1))
  refine ⟨by omega,?_,?_,?_⟩
  · intro a ha
    have rest : (K.erase a).card ≤ ∑ y ∈ K.erase a, deg L E y := by
      simpa using (Finset.sum_le_sum (f:=fun _ => 1) (fun y hy => one y (mem_of_mem_erase hy)))
    have split := Finset.sum_erase_add K (fun y => deg L E y) ha
    have rc : (K.erase a).card=3 := by
      have q : (K.erase a).card+1 = K.card := card_erase_add_one ha
      omega
    have rw := row a ha
    omega
  · have eq := degree_sum L sym irr S tf p hp
    dsimp only at eq
    change _ = 2*deg L S p + (∑ z ∈ E, (deg L S z + deg L K z)) at eq
    rw [k4] at eq
    have eq' : (∑ z ∈ E, (deg L S z + deg L K z)) =
        (∑ z ∈ E, deg L K z) + (∑ z ∈ E, deg L E z) + (∑ z ∈ E, deg L K z) := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [←Finset.sum_add_distrib]
      exact Finset.sum_congr rfl zrow
    rw [eq'] at eq
    rw [cross_transpose L sym] at sumUpper
    change _ ≤ 8+2*(S.card-5)+∑ z ∈ E, deg L E z
    omega
  · have eq := degree_sum L sym irr S tf p hp
    dsimp only at eq
    change _ = 2*deg L S p + (∑ z ∈ E, (deg L S z + deg L K z)) at eq
    rw [k4] at eq
    have eq' : (∑ z ∈ E, (deg L S z + deg L K z)) =
        (∑ z ∈ E, deg L K z) + (∑ z ∈ E, deg L E z) + (∑ z ∈ E, deg L K z) := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [←Finset.sum_add_distrib]
      exact Finset.sum_congr rfl zrow
    rw [eq'] at eq
    change _ = 8+2*(∑ z ∈ E, deg L K z)+(∑ z ∈ E, deg L E z)
    omega

#print axioms cross_transpose
#print axioms target_link_row_degree
end Erdos151H13
