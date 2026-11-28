import N62TwoGhostCut

namespace Erdos151N62
open Erdős151.Upper Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (E : V→V→Prop) [DecidableRel E]

theorem a12_simple_owner_bound
    (sym : ∀ {a b}, E a b → E b a) (irr : ∀ a, ¬E a a)
    (T : Finset V) (g h : V) (gt : g∉T) (ht : h∉T) (gh : g≠h)
    (tc : T.card=10)
    (cap : ∀ u∈T, row E (insert g (insert h T)) u≤3)
    (tf : ∀ a∈insert g (insert h T), ∀ b∈insert g (insert h T), ∀ c∈insert g (insert h T),
      E a b → E a c → E b c → False) :
    (∑ u∈insert g (insert h T), row E (insert g (insert h T)) u) ≤45 := by
  classical
  let S := insert g (insert h T)
  let J : Finset V := {g,h}
  let Z := T.filter (fun u=> ¬E u g ∧ ¬E u h)
  let W := T.filter (fun u=> (E u g ∧ ¬E u h) ∨ (¬E u g ∧ E u h))
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
  have sumcap : d+t≤30 := by
    have p := sum_le_sum cap
    simp only [←show S=insert g (insert h T) from rfl,split,sum_add_distrib,sum_const,nsmul_eq_mul,tc] at p
    exact p
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
  change (∑ u∈S,row E S u)≤45
  rw [full]
  have into (u : V) (ut : u∈T) : u∈S := by simp [S,ut]
  have gs : g∈S := by simp [S]
  have hs : h∈S := by simp [S]
  by_cases edge : E g h
  · have rcap (u : V) (ut : u∈T) : row E J u≤1 := by
      rw [rowJ]
      by_cases a : E u g <;> by_cases b : E u h <;> simp [a,b]
      exact False.elim (tf u (into u ut) g gs h hs a b edge)
    have r := sum_le_sum rcap
    simp [t,tc] at r
    simp [edge]
    omega
  · have zsub : Z⊆T := filter_subset _ _
    have wsub : W⊆T\Z := by
      intro u hu
      obtain ⟨ut,p⟩ := mem_filter.mp hu
      exact mem_sdiff.mpr ⟨ut,fun uz=>by
        have n := (mem_filter.mp uz).2
        exact p.elim (fun l=>n.1 l.1) (fun l=>n.2 l.2)⟩
    have deficit : t+2*Z.card+W.card=20 := by
      let a (u : V) := if ¬E u g ∧ ¬E u h then (2:Nat) else 0
      let b (u : V) := if (E u g ∧ ¬E u h) ∨ (¬E u g ∧ E u h) then (1:Nat) else 0
      have er (u : V) : row E J u+a u+b u=2 := by
        rw [rowJ]
        by_cases x : E u g <;> by_cases y : E u h <;> simp [a,b,x,y]
      have ea : (∑ u∈T,a u)=2*Z.card := by
        unfold a Z
        rw [←sum_filter]
        simp [Nat.mul_comm]
      have eb : (∑ u∈T,b u)=W.card := by
        unfold b W
        rw [←sum_filter]
        simp
      have q := sum_congr (s₂:=T) rfl (fun u _=>er u)
      rw [sum_add_distrib,sum_add_distrib,ea,eb,sum_const,tc] at q
      exact q
    have near (u : V) (ut : u∈T\Z) : E u g ∨ E u h := by
      obtain ⟨uT,n⟩ := mem_sdiff.mp ut
      by_contra! q
      exact n (mem_filter.mpr ⟨uT,q⟩)
    have lo (u : V) (uz : u∈Z) : row E T u≤3 := by
      have p := cap u (zsub uz)
      change row E S u≤3 at p
      rw [split] at p
      omega
    have hi (u : V) (ur : u∈T\Z) : row E (T\Z) u≤2 := by
      have p := cap u (mem_sdiff.mp ur).1
      change row E S u≤3 at p
      rw [split,rowJ] at p
      have rr : row E (T\Z) u≤row E T u :=
        card_le_card (filter_subset_filter _ sdiff_subset)
      rcases near u ur with a|b
      · rw [if_pos a] at p
        omega
      · rw [if_pos b] at p
        omega
    have zero (u : V) (ur : u∈(T\Z)\W) : row E (T\Z) u=0 := by
      obtain ⟨uR,uW⟩ := mem_sdiff.mp ur
      have uT := (mem_sdiff.mp uR).1
      have both : E u g ∧ E u h := by
        rcases near u uR with a|b
        · exact ⟨a,by by_contra n; exact uW (mem_filter.mpr ⟨uT,Or.inl ⟨a,n⟩⟩)⟩
        · exact ⟨by by_contra n; exact uW (mem_filter.mpr ⟨uT,Or.inr ⟨n,b⟩⟩),b⟩
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨vR,uv⟩ := mem_filter.mp hv
      have vS := into v (mem_sdiff.mp vR).1
      exact (near v vR).elim
        (fun a=>tf u (into u uT) v vS g gs uv both.1 a)
        (fun b=>tf u (into u uT) v vS h hs uv both.2 b)
    have edgeBound := split_directed_at E sym T Z zsub lo hi W wsub zero
    change d≤6*Z.card+2*W.card at edgeBound
    simp [edge]
    omega

#print axioms a12_simple_owner_bound
end Erdos151N62
