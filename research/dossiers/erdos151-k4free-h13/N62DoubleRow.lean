import N62SimpleOwner

namespace Erdos151N62
open Erdős151 Erdős151.Upper Erdos151H12 Erdos151H13 Finset
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]
variable {S X : Finset V}

theorem Dstar_count_of_relation (F : NearOwnerFrame G S X)
    [DecidableRel (DoubleRel G F)]
    (sym : ∀ {a b}, G a b → G b a)
    {u : V} (us : u∈S) (T : Finset V)
    (inj : Set.InjOn (support G S) (Dstar G F u : Set V)) :
    (Dstar G F u).card = row (DoubleRel G F) S u := by
  classical
  have part := fun z (h : z∈Dstar G F u) => near_double_partner G F sym us h
  let p (z : V) : V := if hz : z∈Dstar G F u then Classical.choose (part z hz) else u
  have pp (z : V) (hz : z∈Dstar G F u) : p z∈S ∧ p z≠u ∧ support G S z={u,p z} := by
    unfold p
    rw [dif_pos hz]
    exact Classical.choose_spec (part z hz)
  have eq : (Dstar G F u).image p = S.filter (DoubleRel G F u) := by
    ext v
    constructor
    · intro h
      obtain ⟨x,hx,rfl⟩ := mem_image.mp h
      exact mem_filter.mpr ⟨(pp x hx).1,x,(mem_filter.mp hx).1,(pp x hx).2.2⟩
    · intro h
      obtain ⟨vs,x,xd,sup⟩ := mem_filter.mp h
      have lu : Lone G u x := near_double_lone_of_support G F xd (by simp [sup])
      have hit : x∈Dstar G F u := mem_filter.mpr ⟨xd,lu⟩
      have h := (pp x hit).2.2
      have e : ({u,v}:Finset V)={u,p x} := sup.symm.trans h
      have eqn : v=p x := by
        have vp : v∈({u,p x}:Finset V) := e ▸ (by simp : v∈({u,v}:Finset V))
        simp only [mem_insert,mem_singleton] at vp
        exact vp.resolve_left (drel_ne G F (show DoubleRel G F v u from
          drel_sym G F (show DoubleRel G F u v from ⟨x,xd,sup⟩)))
      exact mem_image.mpr ⟨x,hit,eqn.symm⟩
  have injp : Set.InjOn p (Dstar G F u : Set V) := by
    intro x hx y hy he
    apply inj hx hy
    rw [(pp x hx).2.2,(pp y hy).2.2,he]
  change (Dstar G F u).card = (S.filter (DoubleRel G F u)).card
  rw [←eq,card_image_of_injOn injp]

theorem all_pair_support_inj (F : NearOwnerFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V))
    (out : Disjoint X S) (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (mark : ∀ z∈F.doubles, ∃ u∈F.marks, u∈support G S z) :
    Set.InjOn (support G S) (F.doubles : Set V) := by
  classical
  intro a ha b hb h
  obtain ⟨u,um,ua⟩ := mark a ha
  have l : Lone G u a := near_double_lone_of_support G F ha ua
  have l' : Lone G u b := near_double_lone_of_support G F hb (h ▸ ua)
  exact near_marked_star_injOn G F sym irr sc sf out upper u um
    (mem_filter.mpr ⟨ha,l⟩) (mem_filter.mpr ⟨hb,l'⟩) h

#print axioms Dstar_count_of_relation
#print axioms all_pair_support_inj
end Erdos151N62
