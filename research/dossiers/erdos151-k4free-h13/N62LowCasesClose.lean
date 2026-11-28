import N62ThreePrivateB

namespace Erdos151N62
open Erdős151 Erdős151.Upper Erdos151H12 Erdos151H13 Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]

theorem tight16_low_private_impossible
    (S X H : Finset V)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (tf : TriangleFreeLinks G)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V)) (out : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (deg : ∀ u, (neighbors G u).card≤12)
    (sH : H⊆S) (hH : H.card=2) (iso : ∀ u∈H, ∀ v∈S, ¬G u v)
    (triangleFree : ∀ a∈S, ∀ b∈S, ∀ c∈S, G a b → G a c → G b c → False)
    (cap : ∀ u∈S, ambientLoneRow G X u≤11)
    (hits : (∑ x∈X,lcol G S x)=62 → ∀ g∈H, ambientLoneRow G X g=11)
    (Lcap : (∑ x∈X,lcol G S x)≤62)
    (cases' : (acnt G S X=8 ∧ dcnt G S X=27 ∧ bcnt G S X=4 ∧ ccnt G S X=0) ∨
      (acnt G S X=9 ∧ dcnt G S X=26 ∧ bcnt G S X+ccnt G S X=3 ∧ ccnt G S X≤1) ∨
      (acnt G S X=10 ∧ dcnt G S X=26 ∧ 1≤bcnt G S X ∧ ccnt G S X=0)) : False := by
  classical
  let F := nearFrame G S X sym irr tf sc sf out upper
  let A := acnt G S X
  let B := bcnt G S X
  let C := ccnt G S X
  let D := dcnt G S X
  let L := ∑ x∈X,lcol G S x
  have ma : F.marks.card=A := nearFrame_count_marks G S X sym irr tf sc sf out upper
  have blocked (x : V) (hx : x∈X) := all_exterior_blocked_12 G S sc upper x
    (Finset.disjoint_left.mp out hx)
  have lone : A+C+2*D≤L := exact_lone_column_lower G S X sym irr sf blocked
  change L≤62 at Lcap
  have pr : (privateColumns G S X).card=A+B+C := (exact_private_special_counts G S X).1
  have no (l62 : L=62) (exh : A+C+2*D=L) (big : 35≤A+D) (g : V) (gg : g∈H)
      (gm : g∈F.marks) : False :=
    saturated_marked_ghost_impossible G S X sym irr tf sc sf out upper deg cap big exh.symm
      g (hits l62 g gg) gm
  have cj (h : A+B+C=12) (g : V) (gg : g∈H) (gm : g∉F.marks) :
      ∃ z∈weightedSet X (Ccol G S), Lone G g z := by
    obtain ⟨z,zx,zc,zl⟩ := isolated_unmarked_charges_C G S X sym irr tf sc sf out upper
      (pr.trans h) (sH gg) (iso g gg) gm
    exact ⟨z,mem_filter.mpr ⟨zx,zc⟩,zl⟩
  have hpos : H.Nonempty := card_pos.mp (by omega)
  change (A=8 ∧ D=27 ∧ B=4 ∧ C=0) ∨ (A=9 ∧ D=26 ∧ B+C=3 ∧ C≤1) ∨
    (A=10 ∧ D=26 ∧ 1≤B ∧ C=0) at cases'
  rcases cases' with h8|h9|h10
  · obtain ⟨g,gg⟩ := hpos
    by_cases gm : g∈F.marks
    · exact no (by omega) (by omega) (by omega) g gg gm
    · obtain ⟨z,zs,_⟩ := cj (by omega) g gg gm
      have e : 0<C := card_pos.mpr ⟨z,zs⟩
      omega
  · have uc : (S\F.marks).card=3 := by rw [card_sdiff_of_subset F.markSub,sc,ma]; omega
    have bcap : B≤2 := b_columns_at_most_two_on_three G S X sym irr tf sc sf out upper
      triangleFree uc
    obtain ⟨g,h,gh,hg⟩ := card_eq_two.mp hH
    have gH : g∈H := by simp [hg]
    have hH' : h∈H := by simp [hg]
    by_cases gM : g∈F.marks
    · exact no (by omega) (by omega) (by omega) g gH gM
    by_cases hM : h∈F.marks
    · exact no (by omega) (by omega) (by omega) h hH' hM
    obtain ⟨x,xc,xg⟩ := cj (by omega) g gH gM
    obtain ⟨y,yc,yh⟩ := cj (by omega) h hH' hM
    have ee : x=y := by
      by_contra ne
      have ub : ({x,y} : Finset V)⊆weightedSet X (Ccol G S) := by simp [insert_subset_iff,xc,yc]
      have bc := card_le_card ub
      rw [card_insert_of_notMem (by simp [ne]),card_singleton] at bc
      change 2≤C at bc
      omega
    subst y
    have gx : g∈ls (G:=G) S x := (mem_ls (G:=G) S x).mpr ⟨sH gH,lone_symm G sym xg⟩
    have hx : h∈ls (G:=G) S x := (mem_ls (G:=G) S x).mpr ⟨sH hH',lone_symm G sym yh⟩
    have e : (ls (G:=G) S x).card=1 := ((mem_filter.mp xc).2 : Ccol G S x).2
    have ub : ({g,h} : Finset V)⊆ls (G:=G) S x := by simp [insert_subset_iff,gx,hx]
    have bc := card_le_card ub
    rw [card_insert_of_notMem (by simp [gh]),card_singleton] at bc
    omega
  · have bb : 0<(weightedSet X (Bcol G S)).card := by change 0<B; omega
    obtain ⟨x,hx⟩ := card_pos.mp bb
    obtain ⟨xx,bx⟩ := mem_filter.mp hx
    obtain ⟨u,us,v,vs,uv,edge,_,_,su⟩ := Bcol_adjacent_support G S x sym irr sf (blocked x xx) bx
    have nu := B_support_unmarked G S X sym irr tf sc sf out upper xx bx (show u∈support G S x by simp [su])
    have nv := B_support_unmarked G S X sym irr tf sc sf out upper xx bx (show v∈support G S x by simp [su])
    change u∉F.marks at nu
    change v∉F.marks at nv
    have Ueq : S\F.marks={u,v} := by
      symm
      apply eq_of_subset_of_card_le
      · simp [insert_subset_iff,us,vs,nu,nv]
      · rw [card_sdiff_of_subset F.markSub,sc,ma,card_insert_of_notMem (by simp [uv]),card_singleton]
        omega
    obtain ⟨g,gg⟩ := hpos
    have gm : g∈F.marks := by
      by_contra ng
      have n : g∈S\F.marks := mem_sdiff.mpr ⟨sH gg,ng⟩
      rw [Ueq] at n
      simp only [mem_insert,mem_singleton] at n
      rcases n with rfl|rfl
      · exact iso _ gg _ vs edge
      · exact iso _ gg _ us (sym edge)
    exact no (by omega) (by omega) (by omega) g gg gm

#print axioms tight16_low_private_impossible
end Erdos151N62
