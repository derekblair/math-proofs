import N62GhostDup
import N62GhostDirected
import N62DTotalRel

namespace Erdos151N62
open Erdős151 Erdős151.Upper Erdos151H12 Erdos151H13 Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]
variable {S X : Finset V}

theorem unmarked_ghosts_full_cross (F : NearOwnerFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V)) (out : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (T : Finset V) (g h : V) (gt : g∉T) (ht : h∉T) (gh : g≠h)
    (tc : T.card=10) (se : S=insert g (insert h T))
    (tm : T⊆F.marks) (cap : ∀ u∈T,(Dstar G F u).card≤3)
    (dg : (Dstar G F g).card=10) (dh : (Dstar G F h).card=10)
    (D25 : F.doubles.card=25) :
    ∀ x∈T, DoubleRel G F g x ∧ DoubleRel G F h x := by
  classical
  let H : Finset V := {g,h}
  let U := F.doubles.filter (fun z=>support G S z=H)
  let F0 : NearOwnerFrame G S X :=
    { F with doubles := F.doubles\U
             dblData := fun z hz => F.dblData z (mem_sdiff.mp hz).1 }
  let E := DoubleRel G F0
  have es : ∀ {a b}, E a b → E b a := fun {_ _} x=>drel_sym G F0 x
  have ei : ∀ a, ¬E a a := fun _ x=>drel_ne G F0 x rfl
  have gs : g∈S := by simp [se]
  have hs : h∈S := by simp [se]
  have ts : T⊆S := by intro x hx; simp [se,hx]
  have uH : U.card≤2 := by
    have hc : H.card=2 := by simp [H,card_insert_of_notMem,gh]
    have q := three_owner_double_cap G F sym irr sc sf out upper H U (by omega)
      (by simp [H,insert_subset_iff,gs,hs]) (filter_subset _ _)
      (fun z hz => by rw [(mem_filter.mp hz).2])
    omega
  have hpair : ¬E g h := by
    rintro ⟨z,zd,e⟩
    exact (mem_sdiff.mp zd).2 (mem_filter.mpr ⟨(mem_sdiff.mp zd).1,e⟩)
  have am (z : V) (zd : z∈F0.doubles) : ∃ u∈F0.marks, u∈support G S z := by
    obtain ⟨_,a,as,b,bs,ab,_,_,eq⟩ := F0.dblData z zd
    rw [se,mem_insert,mem_insert] at as bs
    rcases as with rfl|rfl|at0
    · rcases bs with rfl|rfl|bt
      · exact False.elim (ab rfl)
      · exact False.elim ((mem_sdiff.mp zd).2 (mem_filter.mpr ⟨(mem_sdiff.mp zd).1,eq⟩))
      · exact ⟨b,tm bt,by simp [eq]⟩
    · rcases bs with rfl|rfl|bt
      · exact False.elim ((mem_sdiff.mp zd).2 (mem_filter.mpr ⟨(mem_sdiff.mp zd).1,by rw [eq]; exact pair_comm _ _⟩))
      · exact False.elim (ab rfl)
      · exact ⟨b,tm bt,by simp [eq]⟩
    · exact ⟨a,tm at0,by simp [eq]⟩
  have inj := all_pair_support_inj G F0 sym irr sc sf out upper am
  have rowEq (u : V) (us : u∈S) : (Dstar G F0 u).card=row E S u := by
    apply Dstar_count_of_relation G F0 sym us S
    intro x hx y hy e
    exact inj (mem_filter.mp hx).1 (mem_filter.mp hy).1 e
  have orig (u : V) : Dstar G F0 u=Dstar G F u\U := by
    ext z
    have eq : F0.doubles=F.doubles\U := rfl
    simp only [Dstar,eq,mem_filter,mem_sdiff]
    tauto
  have crosses (x : V) (xt : x∈T) : Dstar G F0 x=Dstar G F x := by
    rw [orig]
    apply sdiff_eq_left.mpr
    apply Finset.disjoint_left.mpr
    intro z zd zu
    have lx := (mem_filter.mp zd).2
    have xz : x∈support G S z := mem_filter.mpr ⟨ts xt,sym lx.1⟩
    rw [(mem_filter.mp zu).2] at xz
    simp only [H,mem_insert,mem_singleton] at xz
    rcases xz with rfl|rfl
    · exact gt xt
    · exact ht xt
  have uSub (a : V) (ha : a∈H) : U⊆Dstar G F a := by
    intro z hz
    obtain ⟨zd,eq⟩ := mem_filter.mp hz
    have az : a∈support G S z := by rw [eq]; exact ha
    exact mem_filter.mpr ⟨zd,near_double_lone_of_support G F zd az⟩
  have gLen : (Dstar G F0 g).card=10-U.card := by
    rw [orig,card_sdiff_of_subset (uSub g (by simp [H])),dg]
  have hLen : (Dstar G F0 h).card=10-U.card := by
    rw [orig,card_sdiff_of_subset (uSub h (by simp [H])),dh]
  have dtotal := drel_total_of_injective G F0 sym inj
  have dr : F0.doubles.card=25-U.card := by
    change (F.doubles\U).card=_
    rw [card_sdiff_of_subset (filter_subset _ _),D25]
  have gRow : row E T g=10-U.card := by
    have ge := rowEq g gs
    rw [gLen] at ge
    obtain ⟨spl,gj,_,_⟩ := ghost_directed_counts E es ei T g h gt ht gh
    rw [←se] at spl
    rw [spl,gj,if_neg (ei g),if_neg hpair,zero_add,add_zero] at ge
    exact ge.symm
  have hRow : row E T h=10-U.card := by
    have he := rowEq h hs
    rw [hLen] at he
    obtain ⟨spl,gj,_,_⟩ := ghost_directed_counts E es ei T g h gt ht gh
    rw [←se] at spl
    rw [spl,gj,if_neg (fun x=>hpair (es x)),if_neg (ei h),zero_add,add_zero] at he
    exact he.symm
  let Lg := T.filter (E g)
  let Lh := T.filter (E h)
  let K := Lg∩Lh
  have lg : Lg.card=10-U.card := gRow
  have lh : Lh.card=10-U.card := hRow
  have kt : K⊆T := inter_subset_left.trans (filter_subset _ _)
  have ksum := card_union_add_card_inter Lg Lh
  have kunion : (Lg∪Lh).card≤10 := (card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))).trans_eq tc
  have ccap (x : V) (xt : x∈T) : row E S x≤3 := by
    rw [←rowEq x (ts xt),crosses x xt]
    exact cap x xt
  have t3 : ∀ x∈T,row E S x=3 := by
    have sum : (∑ x∈T,row E S x)=30 := by
      change (∑ u∈S,row E S u)=2*F0.doubles.card at dtotal
      have q : (∑ u∈S,row E S u)=row E S g+(row E S h+(∑ u∈T,row E S u)) := by
        calc
          (∑ u∈S,row E S u) = ∑ u∈insert g (insert h T),row E S u :=
            congrArg (fun k : Finset V => ∑ u∈k,row E S u) se
          _ = _ := by rw [sum_insert (by simp [gh,gt]),sum_insert ht]
      have g1 := rowEq g gs
      have h1 := rowEq h hs
      rw [gLen] at g1
      rw [hLen] at h1
      rw [dr] at dtotal
      omega
    intro x xt
    by_contra! bad
    have q := sum_lt_sum ccap ⟨x,xt,show row E S x<3 by have := ccap x xt; omega⟩
    simp [sum,tc] at q
  have zero : U.card=0 := by
    by_contra! nonz
    have cs : U.card=1 ∨ U.card=2 := by omega
    rcases cs with h1|h2
    · obtain ⟨z,ze⟩ := card_eq_one.mp h1
      have zu : z∈U := by simp [ze]
      obtain ⟨zd,zsup⟩ := mem_filter.mp zu
      let B := T\K
      have no : ∀ x∈K,∀ y∈K,¬E x y := by
        intro x xK y yK edge
        obtain ⟨xg,xh⟩ := mem_inter.mp xK
        obtain ⟨yg,yh⟩ := mem_inter.mp yK
        have lift {a b : V} (e : E a b) : DoubleRel G F a b := by
          obtain ⟨p,pd,pe⟩ := e
          exact ⟨p,(mem_sdiff.mp pd).1,pe⟩
        exact ghost_pair_common_independent G F sym irr sc sf out upper (tm (kt xK)) (tm (kt yK))
          ⟨z,zd,zsup⟩ (drel_sym G F (lift (mem_filter.mp xg).2))
          (drel_sym G F (lift (mem_filter.mp xh).2)) (drel_sym G F (lift (mem_filter.mp yg).2))
          (drel_sym G F (lift (mem_filter.mp yh).2)) (lift edge)
      have each (x : V) (xK : x∈K) : 1≤row E B x := by
        have t := t3 x (kt xK)
        obtain ⟨spl,rj,_,_⟩ := ghost_directed_counts E es ei T g h gt ht gh
        rw [←se] at spl
        obtain ⟨xg,xh⟩ := mem_inter.mp xK
        rw [spl,rj,if_pos (es (mem_filter.mp xg).2),if_pos (es (mem_filter.mp xh).2)] at t
        have r : T.filter (E x)⊆B.filter (E x) := by
          intro a ha
          obtain ⟨at0,e⟩ := mem_filter.mp ha
          exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨at0,fun ak=>no x xK a ak e⟩,e⟩
        have p := card_le_card r
        change row E T x≤row E B x at p
        omega
      have bnd (x : V) (xb : x∈B) : row E K x≤3 := by
        have s : K⊆S := kt.trans ts
        have p := card_le_card (filter_subset_filter (E x) s)
        have c := ccap x (mem_sdiff.mp xb).1
        exact p.trans c
      have sw : (∑ x∈K,row E B x)=∑ x∈B,row E K x := by
        have h := transpose E K B
        unfold incidence at h
        have f (x : V) : K.filter (fun y=>E y x)=K.filter (E x) := by
          ext y
          simp only [mem_filter]
          exact and_congr_right (fun _=>⟨es,es⟩)
        simp only [f] at h
        exact h.symm
      have lb := sum_le_sum (f:=fun _=>(1:Nat)) each
      have ub := sum_le_sum (g:=fun _=>(3:Nat)) bnd
      simp only [sum_const,nsmul_eq_mul,mul_one] at lb ub
      change K.card≤∑ x∈K,row E B x at lb
      change (∑ x∈B,row E K x)≤B.card*3 at ub
      have bc : B.card=10-K.card := by rw [card_sdiff_of_subset kt,tc]
      change _+K.card=_ at ksum
      omega
    · obtain ⟨x,y,xy,e⟩ := card_eq_two.mp h2
      have xx : x∈U := by simp [e]
      have yy : y∈U := by simp [e]
      obtain ⟨xd,xe⟩ := mem_filter.mp xx
      obtain ⟨yd,ye⟩ := mem_filter.mp yy
      have kz : K.card=0 := by
        apply card_eq_zero.mpr
        apply not_nonempty_iff_eq_empty.mp
        rintro ⟨z,hz⟩
        obtain ⟨zg,zh⟩ := mem_inter.mp hz
        obtain ⟨a,ad,ae⟩ := (mem_filter.mp zg).2
        obtain ⟨b,bd,be⟩ := (mem_filter.mp zh).2
        exact duplicate_ghost_no_common G F sym irr sc sf out upper xd yd xy xe ye
          ⟨a,(mem_sdiff.mp ad).1,ae⟩ ⟨b,(mem_sdiff.mp bd).1,be⟩
      change _+K.card=_ at ksum
      omega
  intro x xt
  have eg : Lg=T := eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  have eh : Lh=T := eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  have gg : x∈Lg := eg ▸ xt
  have hh : x∈Lh := eh ▸ xt
  obtain ⟨a,ad,ae⟩ := (mem_filter.mp gg).2
  obtain ⟨b,bd,be⟩ := (mem_filter.mp hh).2
  exact ⟨⟨a,(mem_sdiff.mp ad).1,ae⟩,⟨b,(mem_sdiff.mp bd).1,be⟩⟩

#print axioms unmarked_ghosts_full_cross
end Erdos151N62
