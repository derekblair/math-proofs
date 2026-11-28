import N62LoneRowCaps

namespace Erdos151N62
open Erdős151 Erdős151.Upper Erdos151H12 Erdos151H13 Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]

theorem saturated_marked_ghost_impossible
    (S X : Finset V)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (tf : TriangleFreeLinks G)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V)) (out : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (deg : ∀ u, (neighbors G u).card≤12)
    (cap : ∀ u∈S, ambientLoneRow G X u≤11)
    (large : 35≤acnt G S X+dcnt G S X)
    (eq : (∑ x∈X,lcol G S x)=acnt G S X+ccnt G S X+2*dcnt G S X)
    (g : V) (hit : ambientLoneRow G X g=11)
    (gm : g∈(nearFrame G S X sym irr tf sc sf out upper).marks) : False := by
  classical
  let F := nearFrame G S X sym irr tf sc sf out upper
  let Y := X.filter (Lone G g)
  let D := Dstar G F g
  have gs := F.markSub gm
  have p := marked_private_full G S X sym irr tf sc sf out upper gm
  have vertBlock (x : V) (hx : x∈X) := all_exterior_blocked_12 G S sc upper x
    (Finset.disjoint_left.mp out hx)
  have noLeafD : F.leaf g∉D := by
    intro hd
    obtain ⟨_,u,_,v,_,uv,_,_,e⟩ := F.dblData _ (mem_filter.mp hd).1
    have one := near_single_support G F sym gm
    have h2 : (support G S (F.leaf g)).card=2 := by
      rw [e]; simp [card_insert_of_notMem,uv]
    simp [one] at h2
  have deq : Y=insert (F.leaf g) D := by
    ext x
    constructor
    · intro h
      obtain ⟨hx,lx⟩ := mem_filter.mp h
      have gls := (mem_ls (G:=G) S x).mpr ⟨gs,lone_symm G sym lx⟩
      have lc : 0<lcol G S x := card_pos.mpr ⟨g,gls⟩
      rcases exhausted_lone_class G S X sym irr sf vertBlock eq hx lc with a|c|d
      · have q : x∈privateFirst G S X g := mem_filter.mpr
          ⟨hx,Or.inl ⟨Or.inl a,lone_support_subset (G:=G) S x gls⟩⟩
        rw [p.1,mem_singleton] at q
        exact mem_insert.mpr (Or.inl q)
      · have q : x∈privateFirst G S X g := mem_filter.mpr ⟨hx,Or.inr ⟨c,gls⟩⟩
        rw [p.1,mem_singleton] at q
        exact mem_insert.mpr (Or.inl q)
      · exact mem_insert.mpr (Or.inr (mem_filter.mpr ⟨mem_filter.mpr ⟨hx,d⟩,lx⟩))
    · intro h
      rcases mem_insert.mp h with rfl|hd
      · exact mem_filter.mpr ⟨(F.leafData g gm).1,(F.leafData g gm).2.1⟩
      · exact mem_filter.mpr ⟨(F.dblData x (mem_filter.mp hd).1).1,(mem_filter.mp hd).2⟩
  have ten : D.card=10 := by
    change Y.card=11 at hit
    rw [deq,card_insert_of_notMem noLeafD] at hit
    omega
  have starCap (u : V) (hu : u∈S) : (Dstar G F u).card≤11 := by
    have h := card_le_card (s:=Dstar G F u) (t:=X.filter (Lone G u)) (by
      intro z hz
      exact mem_filter.mpr ⟨(F.dblData z (mem_filter.mp hz).1).1,(mem_filter.mp hz).2⟩)
    have c := cap u hu
    change _≤ambientLoneRow G X u at h
    omega
  have l : 35≤F.marks.card+F.doubles.card := by
    have h := nearFrame_count_marks G S X sym irr tf sc sf out upper
    change F.marks.card=acnt G S X at h
    change 35≤F.marks.card+dcnt G S X
    rw [h]
    exact large
  exact near_ten_marked_star_impossible G F sym irr sc sf out upper deg starCap l g gm ten

#print axioms saturated_marked_ghost_impossible
end Erdos151N62
