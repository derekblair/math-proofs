import N62MarkedCrossCut

namespace Erdos151N62
open Erdős151.Upper Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (E : V→V→Prop) [DecidableRel E]

theorem a10_b_simple_owner_bound
    (sym : ∀ {a b}, E a b → E b a) (irr : ∀ a, ¬E a a)
    (T : Finset V) (g h : V) (gt : g∉T) (ht : h∉T) (gh : g≠h)
    (tc : T.card=10) (p q : V) (pt : p∈T) (qt : q∈T) (pq : p≠q)
    (notpq : ¬ E p q) (noCommon : ¬(E p g ∧ E q g) ∧ ¬(E p h ∧ E q h))
    (cap : ∀ u∈T, row E (insert g (insert h T)) u≤3+(if u=p ∨ u=q then 1 else 0))
    (tf : ∀ a∈insert g (insert h T), ∀ b∈insert g (insert h T), ∀ c∈insert g (insert h T),
      a≠p → a≠q → b≠p → b≠q → c≠p → c≠q → E a b → E a c → E b c → False) :
    (∑ u∈insert g (insert h T), row E (insert g (insert h T)) u) ≤49 := by
  classical
  let S := insert g (insert h T)
  let J : Finset V := {g,h}
  let d := ∑ u∈T,row E T u
  let t := ∑ u∈T,row E J u
  have split (u : V) : row E S u=row E T u+row E J u := by
    have eu : T∪J=S := by ext v; simp [S,J]
    have dis : Disjoint T J := by simp [J,gt,ht]
    unfold row
    rw [←eu,filter_union,card_union_of_disjoint]
    exact (dis.mono_left (filter_subset _ _)).mono_right (filter_subset _ _)
  have rowJ (u : V) : row E J u = (if E u g then 1 else 0)+(if E u h then 1 else 0) := by
    unfold row
    by_cases a : E u g <;> by_cases b : E u h <;> simp [J,filter_insert,filter_singleton,a,b,gh]
  have ind : (∑ u∈T, (if u=p ∨ u=q then 1 else 0 : Nat))=2 := by
    rw [←sum_filter]
    have e : T.filter (fun u=>u=p ∨ u=q)={p,q} := by
      ext x
      simp only [mem_filter,mem_insert,mem_singleton]
      exact ⟨And.right,fun h=>⟨h.elim (fun e=>e.symm ▸ pt) (fun e=>e.symm ▸ qt),h⟩⟩
    simp [e,pq]
  have sumcap : d+t≤32 := by
    have q := sum_le_sum cap
    simp only [←show S=insert g (insert h T) from rfl,split,sum_add_distrib,sum_const,nsmul_eq_mul,tc] at q
    rw [ind] at q
    exact q
  have tCross : t=row E T g+row E T h := by
    have q := transpose E J T
    unfold incidence at q
    have fl (u : V) : J.filter (fun v=> E v u)=J.filter (E u) := by
      ext v
      simp only [mem_filter]
      exact and_congr_right fun _=>⟨sym,sym⟩
    simp only [fl] at q
    rw [show (∑ u∈T,(J.filter (E u)).card)=t from rfl] at q
    simpa [J,gh,row] using q
  have full : (∑ u∈S,row E S u)=d+2*t+2*(if E g h then 1 else 0) := by
    have notg : g∉insert h T := by simp [gh,gt]
    have f : (∑ u∈T,row E S u)=d+t := by simp only [split,sum_add_distrib,d,t]
    by_cases a : E g h
    · have b := sym a
      rw [show S=insert g (insert h T) from rfl,sum_insert notg,sum_insert ht,f,split g,split h,rowJ,rowJ]
      simp only [irr,a,b,if_true,if_false]
      omega
    · have b : ¬E h g := fun l=>a (sym l)
      rw [show S=insert g (insert h T) from rfl,sum_insert notg,sum_insert ht,f,split g,split h,rowJ,rowJ]
      simp only [irr,a,b,if_false]
      omega
  change (∑ u∈S,row E S u)≤49
  rw [full]
  have into (u : V) (ut : u∈T) : u∈S := by simp [S,ut]
  have gs : g∈S := by simp [S]
  have hs : h∈S := by simp [S]
  have gp : g≠p := fun e=>gt (e.symm ▸ pt)
  have hp : h≠p := fun e=>ht (e.symm ▸ pt)
  have gq : g≠q := fun e=>gt (e.symm ▸ qt)
  have hq : h≠q := fun e=>ht (e.symm ▸ qt)
  by_cases edge : E g h
  · have rcap (u : V) (ut : u∈T) : row E J u≤1+(if u=p ∨ u=q then 1 else 0) := by
      rw [rowJ]
      by_cases up : u=p ∨ u=q
      · simp only [up,ite_true]
        split <;> split <;> omega
      by_cases a : E u g <;> by_cases b : E u h <;> simp [a,b,up]
      exact False.elim (tf u (into u ut) g gs h hs (fun e=>up (Or.inl e)) (fun e=>up (Or.inr e)) gp gq hp hq a b edge)
    have r := sum_le_sum rcap
    simp only [sum_add_distrib,sum_const,nsmul_eq_mul,tc] at r
    rw [ind] at r
    change t≤12 at r
    simp [edge]
    omega
  · let P : Finset V := {p,q}
    let U := T\P
    let f := ∑ u∈U,missGhost E g h u
    let z := (U.filter (fun x=>missGhost E g h x=2)).card
    let fp := missGhost E g h p
    let fq := missGhost E g h q
    have rf (u : V) : row E J u+missGhost E g h u=2 := by
      rw [rowJ]; unfold missGhost
      split <;> split <;> simp_all
    have pT : P⊆T := by simp [P,insert_subset_iff,pt,qt]
    have feq : t+f+fp+fq=20 := by
      have hh := sum_congr (s₂:=T) rfl (fun u _=>rf u)
      rw [sum_add_distrib,sum_const,tc] at hh
      have e := sum_sdiff pT (f:=missGhost E g h)
      have ep : (∑ x∈P,missGhost E g h x)=fp+fq := by simp [P,pq,fp,fq]
      rw [ep] at e
      change f+(fp+fq)=∑ u∈T,missGhost E g h u at e
      change t+(∑ u∈T,missGhost E g h u)=20 at hh
      omega
    have misses : 1≤fp+fq := by
      change 1≤missGhost E g h p+missGhost E g h q
      rcases not_and_or.mp noCommon.1 with pg|qg
      · simp [missGhost,pg]; omega
      · simp [missGhost,qg]; omega
    have up (u : V) (hu : u∈U) : u≠p := fun e=>(mem_sdiff.mp hu).2 (by simp [P,e])
    have uq (u : V) (hu : u∈U) : u≠q := fun e=>(mem_sdiff.mp hu).2 (by simp [P,e])
    have uT : U⊆T := sdiff_subset
    have sp := split_directed_general E sym T P pT
    have epr : (∑ x∈P,row E T x)=row E T p+row E T q := by simp [P,pq]
    rw [epr] at sp
    change d≤2*(row E T p+row E T q)+∑ u∈U,row E U u at sp
    have cp := cap p pt
    have cq := cap q qt
    simp only [true_or,or_true,ite_true,show insert g (insert h T)=S from rfl,split] at cp cq
    have rp := rf p
    have rq := rf q
    change row E J p+fp=2 at rp
    change row E J q+fq=2 at rq
    have marked := marked_two_ghost_cut E sym S U (fun u hu=>into u (uT hu))
      g h gs hs (fun hu=>gt (uT hu)) (fun hu=>ht (uT hu))
      (by intro u hu; simpa [S,up u hu,uq u hu] using cap u (uT hu))
      (by
        intro x y xU yU xy
        exact ⟨fun e=>tf x (into x (uT xU)) y (into y (uT yU)) g gs (up x xU) (uq x xU) (up y yU) (uq y yU) gp gq xy e.1 e.2,
          fun e=>tf x (into x (uT xU)) y (into y (uT yU)) h hs (up x xU) (uq x xU) (up y yU) (uq y yU) hp hq xy e.1 e.2⟩)
    change (∑ u∈U,row E U u)≤2*(f+z) ∧ 2*z≤f at marked
    simp [edge]
    omega

#print axioms a10_b_simple_owner_bound
end Erdos151N62
