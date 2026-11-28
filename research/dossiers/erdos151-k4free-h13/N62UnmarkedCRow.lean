import N62CExchange

namespace Erdos151N62
open Erdős151 Erdős151.Upper Erdos151H12 Erdos151H13 Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]

theorem unmarked_ghost_c_row
    (S X : Finset V)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (tf : TriangleFreeLinks G)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V)) (out : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (pr : (privateColumns G S X).card=12)
    (eq : ∑ x∈X,lcol G S x=acnt G S X+ccnt G S X+2*dcnt G S X)
    {g : V} (gs : g∈S) (iso : ∀ v∈S, ¬G g v)
    (gm : g∉(nearFrame G S X sym irr tf sc sf out upper).marks) :
    let F := nearFrame G S X sym irr tf sc sf out upper
    let Y := by classical exact X.filter (Lone G g)
    ∃ z∈X, Ccol G S z ∧ Lone G g z ∧
      z∉Dstar G F g ∧ Y=insert z (Dstar G F g) := by
  classical
  let F := nearFrame G S X sym irr tf sc sf out upper
  obtain ⟨z,zx,zc,zl⟩ := isolated_unmarked_charges_C G S X sym irr tf sc sf out upper pr gs iso gm
  have blocked (x : V) (hx : x∈X) := all_exterior_blocked_12 G S sc upper x
    (Finset.disjoint_left.mp out hx)
  have gl := (mem_ls (G:=G) S z).mpr ⟨gs,lone_symm G sym zl⟩
  have zf : z∈privateFirst G S X g := mem_filter.mpr ⟨zx,Or.inr ⟨zc,gl⟩⟩
  have zr : z∈privateSecond G S X g := mem_filter.mpr ⟨zx,Or.inr zc,gl⟩
  have n1 := card_pos.mpr ⟨z,zf⟩
  have n2 := card_pos.mpr ⟨z,zr⟩
  have b := private_slots_charged G S X sym irr tf sc sf out upper g gs
  have f : privateFirst G S X g={z} := by
    symm
    apply eq_of_subset_of_card_le (singleton_subset_iff.mpr zf)
    rw [card_singleton]
    omega
  have zn : z∉Dstar G F g := by
    intro hz
    have d : Dcol G S z := (mem_filter.mp (mem_filter.mp hz).1).2
    have a := zc.2
    have b := d.2
    omega
  refine ⟨z,zx,zc,zl,zn,?_⟩
  ext x
  constructor
  · intro h
    obtain ⟨xx,xl⟩ := mem_filter.mp h
    have ll := (mem_ls (G:=G) S x).mpr ⟨gs,lone_symm G sym xl⟩
    have nc : 0<lcol G S x := card_pos.mpr ⟨g,ll⟩
    rcases exhausted_lone_class G S X sym irr sf blocked eq xx nc with a|c|d
    · exfalso
      apply gm
      change g∈S.filter (fun g => (singlesFor G S X g).Nonempty)
      exact mem_filter.mpr ⟨gs,⟨x,(mem_singlesFor G).mpr
        ⟨xx,a,lone_support_subset (G:=G) S x ll⟩⟩⟩
    · have xf : x∈privateFirst G S X g := mem_filter.mpr ⟨xx,Or.inr ⟨c,ll⟩⟩
      rw [f,mem_singleton] at xf
      exact mem_insert.mpr (Or.inl xf)
    · exact mem_insert.mpr (Or.inr (mem_filter.mpr ⟨mem_filter.mpr ⟨xx,d⟩,xl⟩))
  · intro h
    rcases mem_insert.mp h with rfl|hd
    · exact mem_filter.mpr ⟨zx,zl⟩
    · exact mem_filter.mpr ⟨(F.dblData x (mem_filter.mp hd).1).1,(mem_filter.mp hd).2⟩

#print axioms unmarked_ghost_c_row
end Erdos151N62
