import N62NearStar

namespace Erdos151N62
open Erdős151 Erdos151H12 Erdos151H13 Finset
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]
variable {S X : Finset V}

theorem near_Dstar_lone_bound (F : NearOwnerFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) (u : V) :
    (Dstar G F u).card+(if u∈F.marks then 1 else 0) ≤ ambientLoneRow G X u := by
  classical
  let D := Dstar G F u
  let L := X.filter (Lone G u)
  have ds : D⊆L := by
    intro z hz
    obtain ⟨zd,zl⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨(F.dblData z zd).1,zl⟩
  change D.card+(if u∈F.marks then 1 else 0)≤L.card
  by_cases um : u∈F.marks
  · let a := F.leaf u
    have al : a∈L := mem_filter.mpr ⟨(F.leafData u um).1,(F.leafData u um).2.1⟩
    have nd : a∉D := by
      intro ad
      obtain ⟨_,v,_,w,_,vw,_,_,e⟩ := F.dblData a (mem_filter.mp ad).1
      have t : (support G S a).card=2 := by simp [e,card_insert_of_notMem,vw]
      change (support G S (F.leaf u)).card=2 at t
      rw [near_single_support G F sym um,card_singleton] at t
      omega
    have y := card_le_card (insert_subset_iff.mpr ⟨al,ds⟩)
    rw [card_insert_of_notMem nd] at y
    simpa only [if_pos um] using y
  · simpa only [if_neg um,Nat.add_zero] using card_le_card ds

#print axioms near_Dstar_lone_bound
end Erdos151N62
