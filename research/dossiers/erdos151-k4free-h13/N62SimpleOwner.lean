import N62DCounts

namespace Erdos151N62
open Erdős151 Erdős151.Upper Erdos151H12 Erdos151H13 Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]
variable {S X : Finset V}

def DoubleRel (F : NearOwnerFrame G S X) (u v : V) : Prop :=
  ∃ z∈F.doubles, support G S z={u,v}

theorem drel_sym (F : NearOwnerFrame G S X) {u v : V} (h : DoubleRel G F u v) :
    DoubleRel G F v u := by
  obtain ⟨z,zd,e⟩ := h
  exact ⟨z,zd,by rw [e,pair_comm]⟩

theorem drel_ne (F : NearOwnerFrame G S X) {u v : V} (h : DoubleRel G F u v) : u≠v := by
  rintro rfl
  obtain ⟨z,zd,e⟩ := h
  have h := support_two G F zd
  simp [e] at h

theorem drel_owners (F : NearOwnerFrame G S X) {u v : V} (h : DoubleRel G F u v) :
    u∈S ∧ v∈S := by
  obtain ⟨z,zd,e⟩ := h
  have hu : u∈support G S z := by simp [e]
  have hv : v∈support G S z := by simp [e]
  exact ⟨(mem_filter.mp hu).1,(mem_filter.mp hv).1⟩

theorem drel_nonadjacent (F : NearOwnerFrame G S X) {u v : V}
    (sym : ∀ {a b}, G a b → G b a) (h : DoubleRel G F u v) : ¬G u v := by
  obtain ⟨z,zd,e⟩ := h
  have zu := near_double_lone_of_support G F zd (show u∈support G S z by simp [e])
  have zv := near_double_lone_of_support G F zd (show v∈support G S z by simp [e])
  exact fun a => zu.2 v ⟨a,sym zv.1⟩

private theorem support_wrap {S P : Finset V} {z : V} (h : support G S z=P) :
    supported G S P z := fun y hy hG => h ▸ mem_filter.mpr ⟨hy,hG⟩

private theorem different_support {v w : V} {S : Finset V}
    (one : (support G S v).card=1) (two : (support G S w).card=2) : v≠w := by
  intro e
  rw [e,two] at one
  omega

theorem marked_drel_forces_leaf (F : NearOwnerFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V)) (out : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    {u v : V} (um : u∈F.marks) (vm : v∈F.marks) (h : DoubleRel G F u v) :
    Lone G (F.leaf u) (F.leaf v) := by
  have uv := drel_ne G F h
  obtain ⟨z,zd,e⟩ := h
  have lu := F.leafData u um
  have lv := F.leafData v vm
  have za := F.dblData z zd
  have ou (x : V) (hx : x∈X) : x∉S := Finset.disjoint_left.mp out hx
  have su := near_single_support G F sym um
  have sv := near_single_support G F sym vm
  have hne : F.leaf u≠F.leaf v := by
    intro ex
    have e := congrArg (support G S) ex
    rw [su,sv,singleton_inj] at e
    exact uv e
  exact owner_pair_forces_lone G sym irr S u v (F.leaf u) (F.leaf v) z
    (F.markSub um) (F.markSub vm) uv (ou _ lu.1) (ou _ lv.1) (ou _ za.1) hne
    (different_support G (by simp [su]) (support_two G F zd))
    (different_support G (by simp [sv]) (support_two G F zd))
    lu.2.1 lv.2.1
    (near_double_lone_of_support G F zd (by simp [e]))
    (near_double_lone_of_support G F zd (by simp [e]))
    lu.2.2 lv.2.2 (support_wrap G e) sc sf
    (fun T ht hf => by have := upper T hf; omega)

theorem marked_drel_triangle_free (F : NearOwnerFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V)) (out : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    {u v w : V} (um : u∈F.marks) (vm : v∈F.marks) (wm : w∈F.marks)
    (uv : DoubleRel G F u v) (uw : DoubleRel G F u w) (vw : DoubleRel G F v w) : False := by
  have a := marked_drel_forces_leaf G F sym irr sc sf out upper um vm uv
  have b := marked_drel_forces_leaf G F sym irr sc sf out upper um wm uw
  have c := marked_drel_forces_leaf G F sym irr sc sf out upper vm wm vw
  exact a.2 (F.leaf w) ⟨b.1,c.1⟩

#print axioms marked_drel_triangle_free
end Erdos151N62
