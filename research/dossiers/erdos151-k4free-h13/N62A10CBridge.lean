import N62UnmarkedCRow
import N62FullCross
import N62NearCap

namespace Erdos151N62
open Erdős151 Erdős151.Upper Erdos151H12 Erdos151H13 Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]

theorem a10_c_columns_impossible
    (S X T : Finset V) (w g h : V) (gt : g∉T) (ht : h∉T) (gh : g≠h)
    (tc : T.card=10) (se : S=insert g (insert h T)) (wx : w∉X)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (tf : TriangleFreeLinks G)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V)) (out : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (deg : ∀ u, (neighbors G u).card≤12)
    (iso : ∀ u ∈ ({g,h}:Finset V),∀ v∈S, ¬G u v)
    (lw : ∀ u∈({g,h}:Finset V), Lone G u w)
    (cap : ∀ u∈S,ambientLoneRow G X u≤11)
    (capT : ∀ u∈T,ambientLoneRow G X u≤4)
    (hits : (∑ x∈X,lcol G S x)=62 → ∀ r∈({g,h}:Finset V),ambientLoneRow G X r=11)
    (Lcap : (∑ x∈X,lcol G S x)≤62)
    (a10 : acnt G S X=10) (b0 : bcnt G S X=0) (c2 : ccnt G S X=2) (d25 : dcnt G S X=25) :
    False := by
  classical
  let F := nearFrame G S X sym irr tf sc sf out upper
  let H : Finset V := {g,h}
  let L := ∑ x∈X,lcol G S x
  have blk (z : V) (zx : z∈X) := all_exterior_blocked_12 G S sc upper z (Finset.disjoint_left.mp out zx)
  have lo := exact_lone_column_lower G S X sym irr sf blk
  change acnt G S X+ccnt G S X+2*dcnt G S X≤L at lo
  change L≤62 at Lcap
  have l62 : L=62 := by omega
  have e : L=acnt G S X+ccnt G S X+2*dcnt G S X := by omega
  have lc (u : V) (uh : u∈H) : ambientLoneRow G X u=11 := hits l62 u uh
  have lg : g∈H := by simp [H]
  have lh : h∈H := by simp [H]
  have gin : g∈S := by simp [se]
  have hin : h∈S := by simp [se]
  have no (u : V) (uh : u∈H) (m : u∈F.marks) : False :=
    saturated_marked_ghost_impossible G S X sym irr tf sc sf out upper deg cap (by omega) e u (lc u uh) m
  have ng : g∉F.marks := fun gm=>no g lg gm
  have nh : h∉F.marks := fun hm=>no h lh hm
  have mt : F.marks⊆T := by
    intro x xm
    have xs := F.markSub xm
    rw [se,mem_insert,mem_insert] at xs
    rcases xs with rfl|rfl|xt
    · exact False.elim (ng xm)
    · exact False.elim (nh xm)
    · exact xt
  have me : F.marks=T := by
    apply eq_of_subset_of_card_le mt
    rw [tc,(nearFrame_count_marks G S X sym irr tf sc sf out upper).trans a10]
  have pr : (privateColumns G S X).card=12 := by
    rw [(exact_private_special_counts G S X).1,a10,b0,c2]
  obtain ⟨z,zx,zc,zl,zn,zr⟩ := unmarked_ghost_c_row G S X sym irr tf sc sf out upper pr e gin (iso g lg) ng
  obtain ⟨y,yx,yc,yl,yn,yr⟩ := unmarked_ghost_c_row G S X sym irr tf sc sf out upper pr e hin (iso h lh) nh
  have gd : (Dstar G F g).card=10 := by
    have c := lc g lg
    change (X.filter (Lone G g)).card=11 at c
    change X.filter (Lone G g)=insert z (Dstar G F g) at zr
    rw [zr,card_insert_of_notMem zn] at c
    change (Dstar G F g).card+1=11 at c
    omega
  have hd : (Dstar G F h).card=10 := by
    have c := lc h lh
    change (X.filter (Lone G h)).card=11 at c
    change X.filter (Lone G h)=insert y (Dstar G F h) at yr
    rw [yr,card_insert_of_notMem yn] at c
    change (Dstar G F h).card+1=11 at c
    omega
  have cT (u : V) (ut : u∈T) : (Dstar G F u).card≤3 := by
    have b := near_Dstar_lone_bound G F sym u
    have c := capT u ut
    have m : u∈F.marks := me ▸ ut
    rw [if_pos m] at b
    omega
  have d : F.doubles.card=25 := d25
  have full := unmarked_ghosts_full_cross G F sym irr sc sf out upper T g h gt ht gh tc se
    (fun u ut=>me ▸ ut) cT gd hd d
  have gl (x : V) (ga : G h x) : Lone G h x := by
    let E := X.filter (Lone G h)
    have wn : w∉E := fun h=>wx (mem_filter.mp h).1
    have lc' : E.card=11 := lc h lh
    have sub : insert w E ⊆ neighbors G h := by
      intro x hx
      rcases mem_insert.mp hx with rfl|he
      · exact (mem_neighbors G).mpr (lw h lh).1
      · exact (mem_neighbors G).mpr (mem_filter.mp he).2.1
    have eq := eq_of_subset_of_card_le sub (by rw [card_insert_of_notMem wn,lc']; exact deg h)
    have hga : x∈insert w E := eq ▸ (mem_neighbors G).mpr ga
    rcases mem_insert.mp hga with rfl|he
    · exact lw h lh
    · exact (mem_filter.mp he).2
  have gz : g∈ls (G:=G) S z := (mem_ls (G:=G) S z).mpr ⟨gin,lone_symm G sym zl⟩
  have gz' : g∈ns (G:=G) S z := lone_support_subset (G:=G) S z gz
  have ce : (ns (G:=G) S z).card=2 := zc.1
  obtain ⟨u,v,uv,hsup⟩ := card_eq_two.mp ce
  have ghit := gz'
  rw [hsup,mem_insert,mem_singleton] at ghit
  obtain ⟨s,sg,sup⟩ : ∃ s, s≠g ∧ ns (G:=G) S z={g,s} := by
    rcases ghit with rfl|rfl
    · exact ⟨v,uv.symm,hsup⟩
    · exact ⟨u,uv,by rw [hsup,pair_comm]⟩
  have sz : s∈ns (G:=G) S z := by simp [sup]
  have sn := (mem_ns (G:=G) S z).mp sz
  have sh : s≠h := by
    intro sh
    have a : Lone G s z := sh ▸ gl z (sh ▸ sym sn.2)
    have l : s∈ls (G:=G) S z := (mem_ls (G:=G) S z).mpr ⟨sn.1,lone_symm G sym a⟩
    obtain ⟨i,il⟩ := card_eq_one.mp (show (ls (G:=G) S z).card=1 from zc.2)
    have gg : g=i := by simpa [il] using gz
    have ss : s=i := by simpa [il] using l
    exact sg (ss.trans gg.symm)
  have st : s∈T := by
    have hs : s∈S := sn.1
    rw [se,mem_insert,mem_insert] at hs
    exact (hs.resolve_left sg).resolve_left sh
  have sup' : support G S z={g,s} := by
    have eq : support G S z=ns (G:=G) S z := by ext u; simp [support,Support]
    exact eq.trans sup
  exact c_column_plus_double_impossible G F sym irr sc sf out upper (me ▸ st) zx zc zl (sym sn.2) sup' (full s st).1

#print axioms a10_c_columns_impossible
end Erdos151N62
