import N62SaturatedMarkGhost

namespace Erdos151N62
open Erdős151 Erdős151.Upper Erdos151H12 Erdos151H13 Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]

/-- A B-column cannot charge an A-marked owner. -/
theorem B_support_unmarked
    (S X : Finset V)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (tf : TriangleFreeLinks G)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V)) (out : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    {x u : V} (xx : x∈X) (b : Bcol G S x) (us : u∈support G S x) :
    u∉(nearFrame G S X sym irr tf sc sf out upper).marks := by
  classical
  intro um
  have p := marked_private_full G S X sym irr tf sc sf out upper um
  have sn : u∈ns (G:=G) S x := by
    apply (mem_ns (G:=G) S x).mpr
    exact mem_filter.mp us
  have h : x∈privateFirst G S X u := mem_filter.mpr ⟨xx,Or.inl ⟨Or.inr b,sn⟩⟩
  rw [p.1,mem_singleton] at h
  let F := nearFrame G S X sym irr tf sc sf out upper
  have eq := near_single_support G F sym um
  have e : (support G S x).card=2 := by
    have f : support G S x=ns (G:=G) S x := by ext v; simp [support,Support]
    rw [f]
    exact b.1
  change x=F.leaf u at h
  rw [h,eq,card_singleton] at e
  omega

theorem isolated_unmarked_charges_C
    (S X : Finset V)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (tf : TriangleFreeLinks G)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V)) (out : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (pr : (privateColumns G S X).card=12)
    {u : V} (us : u∈S) (iso : ∀ v∈S, ¬G u v)
    (um : u∉(nearFrame G S X sym irr tf sc sf out upper).marks) :
    ∃ x∈X, Ccol G S x ∧ Lone G u x := by
  classical
  let F := nearFrame G S X sym irr tf sc sf out upper
  have e := private_charges_saturated G S X sc sym irr tf sf out upper pr u us
  have hitA (x : V) (xx : x∈X) (a : Acol G S x) (s : u∈ns (G:=G) S x) : False := by
    apply um
    change u∈S.filter (fun u => (singlesFor G S X u).Nonempty)
    exact mem_filter.mpr ⟨us,⟨x,(mem_singlesFor G).mpr ⟨xx,a,s⟩⟩⟩
  have hitC (x : V) (xx : x∈X) (h : Ccol G S x) (s : u∈ls (G:=G) S x) :
      ∃ x∈X, Ccol G S x ∧ Lone G u x :=
    ⟨x,xx,h,lone_symm G sym ((mem_ls (G:=G) S x).mp s).2⟩
  by_cases fst : (privateFirst G S X u).Nonempty
  · obtain ⟨x,hx⟩ := fst
    obtain ⟨xx,h⟩ := mem_filter.mp hx
    rcases h with ⟨a|b,s⟩|⟨c,s⟩
    · exact False.elim (hitA x xx a s)
    · have blocked := all_exterior_blocked_12 G S sc upper x (Finset.disjoint_left.mp out xx)
      obtain ⟨a,as,c,cs,_,ac,_,_,sup⟩ := Bcol_adjacent_support G S x sym irr sf blocked b
      have h : u=a ∨ u=c := by
        have hs : u∈support G S x := mem_filter.mpr ((mem_ns (G:=G) S x).mp s)
        simpa [sup] using hs
      rcases h with rfl|rfl
      · exact False.elim (iso c cs ac)
      · exact False.elim (iso a as (sym ac))
    · exact hitC x xx c s
  · have hzero := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp fst)
    have pos : 0<(privateSecond G S X u).card := by omega
    obtain ⟨x,hx⟩ := card_pos.mp pos
    obtain ⟨xx,t,s⟩ := mem_filter.mp hx
    rcases t with a|c
    · exact False.elim (hitA x xx a (lone_support_subset (G:=G) S x s))
    · exact hitC x xx c s

#print axioms B_support_unmarked
#print axioms isolated_unmarked_charges_C
end Erdos151N62
