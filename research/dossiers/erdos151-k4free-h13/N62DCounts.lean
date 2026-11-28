import N62NearStar

namespace Erdos151N62
open Erdős151 Erdős151.Upper Erdos151H12 Erdos151H13 Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]
variable {S X : Finset V}

noncomputable def degreeBucket (F : NearOwnerFrame G S X) (T : Finset V) (i : Nat) : Finset V := by
  exact weightedSet F.doubles (fun z => (support G S z∩T).card=i)

theorem mem_degreeBucket (F : NearOwnerFrame G S X) (T : Finset V) (i : Nat) (z : V) :
    z∈degreeBucket G F T i ↔ z∈F.doubles ∧ (support G S z∩T).card=i := by
  simp [degreeBucket,weightedSet]

theorem support_two (F : NearOwnerFrame G S X) {z : V} (hz : z∈F.doubles) :
    (support G S z).card=2 := by
  obtain ⟨_,u,_,v,_,ne,_,_,eq⟩ := F.dblData z hz
  simp [eq,card_insert_of_notMem,ne]

theorem dstar_count_on (F : NearOwnerFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) (T : Finset V) (ts : T⊆S) :
    (∑ u∈T,(Dstar G F u).card) =
      (degreeBucket G F T 1).card + 2*(degreeBucket G F T 2).card := by
  classical
  let D := F.doubles
  let R (u z : V) : Prop := Lone G u z
  have tr := (transpose R T D).symm
  change (∑ u∈T,(Dstar G F u).card) = ∑ z∈D,(T.filter (fun u=>Lone G u z)).card at tr
  rw [tr]
  have bd (z : V) (hz : z∈D) :
      (T.filter (fun u=>Lone G u z)).card = (support G S z∩T).card := by
    congr 1
    ext u
    rw [mem_filter,mem_inter]
    constructor
    · rintro ⟨ut,l⟩
      exact ⟨mem_filter.mpr ⟨ts ut,sym l.1⟩,ut⟩
    · rintro ⟨us,ut⟩
      exact ⟨ut,near_double_lone_of_support G F hz us⟩
  let a (z : V) := if (support G S z∩T).card=1 then 1 else 0
  let b (z : V) := if (support G S z∩T).card=2 then 2 else 0
  have ha := indicator_count_flexible D (fun z => (support G S z∩T).card=1) 1 a
    (fun z hz h => by simp [a,h]) (fun z hz h => by simp [a,h])
  have hb := indicator_count_flexible D (fun z => (support G S z∩T).card=2) 2 b
    (fun z hz h => by simp [b,h]) (fun z hz h => by simp [b,h])
  change 1*(degreeBucket G F T 1).card = ∑ z∈D,a z at ha
  change 2*(degreeBucket G F T 2).card = ∑ z∈D,b z at hb
  rw [←one_mul (degreeBucket G F T 1).card, ha, hb,←sum_add_distrib]
  apply sum_congr rfl
  intro z hz
  rw [bd z hz]
  have h := (card_le_card (s:=support G S z∩T) (t:=support G S z) inter_subset_left)
  rw [support_two G F hz] at h
  have cases' : (support G S z∩T).card=0 ∨ (support G S z∩T).card=1 ∨
      (support G S z∩T).card=2 := by omega
  rcases cases' with h|h|h <;> simp [a,b,h]

theorem dstar_bucket_total (F : NearOwnerFrame G S X) (T : Finset V) :
    F.doubles.card=(degreeBucket G F T 0).card+(degreeBucket G F T 1).card+
      (degreeBucket G F T 2).card := by
  classical
  let D0 := degreeBucket G F T 0
  let D1 := degreeBucket G F T 1
  let D2 := degreeBucket G F T 2
  have d01 : Disjoint D0 D1 := Finset.disjoint_left.mpr (by
    intro z h0 h1
    have a : (support G S z∩T).card=0 := ((mem_degreeBucket G F T _ _).mp h0).2
    have b : (support G S z∩T).card=1 := ((mem_degreeBucket G F T _ _).mp h1).2
    omega)
  have d02 : Disjoint D0 D2 := Finset.disjoint_left.mpr (by
    intro z h0 h1
    have a : (support G S z∩T).card=0 := ((mem_degreeBucket G F T _ _).mp h0).2
    have b : (support G S z∩T).card=2 := ((mem_degreeBucket G F T _ _).mp h1).2
    omega)
  have d12 : Disjoint D1 D2 := Finset.disjoint_left.mpr (by
    intro z h0 h1
    have a : (support G S z∩T).card=1 := ((mem_degreeBucket G F T _ _).mp h0).2
    have b : (support G S z∩T).card=2 := ((mem_degreeBucket G F T _ _).mp h1).2
    omega)
  have eq : F.doubles=(D0∪D1)∪D2 := by
    ext z
    constructor
    · intro hz
      have h := card_le_card (s:=support G S z∩T) (t:=support G S z) inter_subset_left
      rw [support_two G F hz] at h
      have cases' : (support G S z∩T).card=0 ∨ (support G S z∩T).card=1 ∨
        (support G S z∩T).card=2 := by omega
      rcases cases' with h|h|h
      · exact mem_union_left _ (mem_union_left _ ((mem_degreeBucket G F T _ _).mpr ⟨hz,h⟩))
      · exact mem_union_left _ (mem_union_right _ ((mem_degreeBucket G F T _ _).mpr ⟨hz,h⟩))
      · exact mem_union_right _ ((mem_degreeBucket G F T _ _).mpr ⟨hz,h⟩)
    · intro h
      rcases mem_union.mp h with h|h
      · rcases mem_union.mp h with h|h
        · exact ((mem_degreeBucket G F T _ _).mp h).1
        · exact ((mem_degreeBucket G F T _ _).mp h).1
      · exact ((mem_degreeBucket G F T _ _).mp h).1
  change F.doubles.card=D0.card+D1.card+D2.card
  rw [eq,card_union_of_disjoint (disjoint_union_left.mpr ⟨d02,d12⟩),card_union_of_disjoint d01]

#print axioms dstar_count_on
#print axioms dstar_bucket_total
end Erdos151N62
