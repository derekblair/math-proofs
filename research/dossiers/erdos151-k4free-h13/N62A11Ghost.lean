import N62GhostDirected
import N62DTotalRel
import N62GhostPressure
import N62DirectedSplit

namespace Erdos151N62
open Erdős151 Erdős151.Upper Erdos151H12 Erdos151H13 Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]
variable {S X : Finset V}

theorem a11_unmarked_ghost_excluded (F : NearOwnerFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V)) (out : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (deg : ∀ x,(neighbors G x).card≤12)
    (T : Finset V) (g h : V) (gt : g∉T) (ht : h∉T) (gh : g≠h)
    (tc : T.card=10) (se : S=insert g (insert h T))
    (gm : g∈F.marks) (tm : T⊆F.marks)
    (cap : ∀ u∈T,(Dstar G F u).card≤3)
    (big : 24≤F.doubles.card) : False := by
  classical
  let E := DoubleRel G F
  let es : ∀ {a b}, E a b → E b a := fun {_ _} t=>drel_sym G F t
  have ei : ∀ a, ¬E a a := fun u t => drel_ne G F t rfl
  have ms : ∀ x∈S, x≠h → x∈F.marks := by
    intro x xs xh
    rw [se,mem_insert,mem_insert] at xs
    rcases xs with rfl|rfl|xt
    · exact gm
    · exact False.elim (xh rfl)
    · exact tm xt
  have inj := all_pair_support_inj G F sym irr sc sf out upper (by
    intro z dz
    obtain ⟨_,a,as,b,bs,ab,_,_,eq⟩ := F.dblData z dz
    by_cases ea : a=h
    · have bm := ms b bs (fun h => ab (ea.trans h.symm))
      exact ⟨b,bm,by simp [eq]⟩
    · exact ⟨a,ms a as ea,by simp [eq]⟩)
  have rowEq (u : V) (us : u∈S) : (Dstar G F u).card=row E S u := by
    apply Dstar_count_of_relation G F sym us S
    intro x hx y hy eq
    exact inj (mem_filter.mp hx).1 (mem_filter.mp hy).1 eq
  have gcap (x : V) (xt : x∈T) : row E S x≤3 := by
    rw [←rowEq x (by simp [se,xt])]
    exact cap x xt
  let J : Finset V := {g,h}
  let d := ∑ u∈T,row E T u
  let t := ∑ u∈T,row E J u
  obtain ⟨split,rJ,tcross,full⟩ := ghost_directed_counts E es ei T g h gt ht gh
  rw [←se] at split full
  change (∑ u∈S,row E S u)=d+2*t+2*(if E g h then 1 else 0) at full
  have dtotal := drel_total_of_injective G F sym inj
  change (∑ u∈S,row E S u)=2*F.doubles.card at dtotal
  have sp : d+t≤30 := by
    have p := sum_le_sum gcap
    simp only [split,sum_add_distrib,sum_const,nsmul_eq_mul,tc] at p
    exact p
  let Lg := T.filter (E g)
  let Lh := T.filter (E h)
  have lgt : Lg⊆T := filter_subset _ _
  have lht : Lh⊆T := filter_subset _ _
  have cross : t=Lg.card+Lh.card := tcross
  have cg : Lg.card≤10 := (card_le_card lgt).trans_eq tc
  have ch : Lh.card≤10 := (card_le_card lht).trans_eq tc
  by_cases eh : E g h
  · rw [if_pos eh] at full
    have c := card_union_add_card_inter Lg Lh
    have ub : (Lg∪Lh).card≤10 := (card_le_card (union_subset lgt lht)).trans_eq tc
    have pressure := near_marked_ghost_book_pressure G F sym irr sc sf out upper T g h gt ht tm gm eh
    have gg : weightedSet T (E g)=Lg := by ext x; simp [weightedSet,Lg]
    have hg : weightedSet T (E h)=Lh := by ext x; simp [weightedSet,Lh]
    change 1+(weightedSet T (E g)).card+(weightedSet T (E g)∩weightedSet T (E h)).card≤_ at pressure
    rw [gg,hg] at pressure
    have md := deg (F.leaf g)
    omega
  · rw [if_neg eh] at full
    let Z := T\Lg
    have zt : Z⊆T := sdiff_subset
    have zero (x : V) (xt : x∈T\Z) : row E (T\Z) x=0 := by
      apply card_eq_zero.mpr
      apply not_nonempty_iff_eq_empty.mp
      rintro ⟨y,hy⟩
      have yT := (mem_filter.mp hy).1
      have ey := (mem_filter.mp hy).2
      have lg : T\Z=Lg := Finset.sdiff_sdiff_eq_self lgt
      rw [lg] at xt yT
      exact marked_drel_triangle_free G F sym irr sc sf out upper gm
        (tm (lgt xt)) (tm (lgt yT)) (mem_filter.mp xt).2 (mem_filter.mp yT).2 ey
    have sub := split_directed_general E es T Z zt
    have ze : (∑ x∈T\Z,row E (T\Z) x)=0 := sum_eq_zero zero
    rw [ze,add_zero] at sub
    let Q := Z.filter (fun x=> ¬E x h)
    have rowCap (x : V) (hx : x∈Z) :
        row E T x≤2+(if ¬E x h then 1 else 0) := by
      have xs := zt hx
      have ng : ¬E x g := fun hxg => (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨xs,es hxg⟩)
      have hh := gcap x xs
      rw [split,rJ,if_neg ng,zero_add] at hh
      by_cases e : E x h <;> simp [e] at hh ⊢ <;> omega
    have m := sum_le_sum rowCap
    rw [sum_add_distrib] at m
    have yy : (∑ x∈Z,(if ¬E x h then (1:Nat) else 0))=Q.card := by
      unfold Q
      rw [←sum_filter]
      simp
    rw [yy] at m
    simp only [sum_const,nsmul_eq_mul] at m
    have qb : Q⊆T\Lh := by
      intro x hx
      obtain ⟨hx,hnh⟩ := mem_filter.mp hx
      exact mem_sdiff.mpr ⟨zt hx,fun hl=>hnh (es (mem_filter.mp hl).2)⟩
    have qcb := card_le_card qb
    rw [card_sdiff_of_subset lht,tc] at qcb
    have zc : Z.card=10-Lg.card := by rw [card_sdiff_of_subset lgt,tc]
    change d≤2*(∑ u∈Z,row E T u) at sub
    change (∑ x∈Z,row E T x)≤Z.card*2+Q.card at m
    omega

#print axioms a11_unmarked_ghost_excluded
end Erdos151N62
