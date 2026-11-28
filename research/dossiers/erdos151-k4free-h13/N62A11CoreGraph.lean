import N62MarkedCrossCut

namespace Erdos151N62
open Erdős151.Upper Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (E : V→V→Prop) [DecidableRel E]

theorem a11_core_simple_owner_bound
    (sym : ∀ {a b}, E a b → E b a) (irr : ∀ a, ¬E a a)
    (T : Finset V) (g h : V) (gt : g∉T) (ht : h∉T) (gh : g≠h)
    (tc : T.card=10) (p : V) (pt : p∈T)
    (cap : ∀ u∈T, row E (insert g (insert h T)) u≤3+(if u=p then 1 else 0))
    (tf : ∀ a∈insert g (insert h T), ∀ b∈insert g (insert h T), ∀ c∈insert g (insert h T),
      a≠p → b≠p → c≠p → E a b → E a c → E b c → False) :
    (∑ u∈insert g (insert h T), row E (insert g (insert h T)) u) ≤47 := by
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
  have sumcap : d+t≤31 := by
    have q := sum_le_sum cap
    simp only [←show S=insert g (insert h T) from rfl,split,sum_add_distrib,sum_const,nsmul_eq_mul,tc] at q
    have ind : (∑ u∈T, (if u=p then 1 else 0 : Nat))=1 := by simp [pt]
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
  change (∑ u∈S,row E S u)≤47
  rw [full]
  have into (u : V) (ut : u∈T) : u∈S := by simp [S,ut]
  have gs : g∈S := by simp [S]
  have hs : h∈S := by simp [S]
  have gp : g≠p := fun e=>gt (e.symm ▸ pt)
  have hp : h≠p := fun e=>ht (e.symm ▸ pt)
  by_cases edge : E g h
  · have rcap (u : V) (ut : u∈T) : row E J u≤1+(if u=p then 1 else 0) := by
      rw [rowJ]
      by_cases up : u=p
      · simp only [up,ite_true]
        split <;> split <;> omega
      by_cases a : E u g <;> by_cases b : E u h <;> simp [a,b,up]
      exact False.elim (tf u (into u ut) g gs h hs up gp hp a b edge)
    have r := sum_le_sum rcap
    simp only [sum_add_distrib,sum_const,nsmul_eq_mul,tc] at r
    have ind : (∑ u∈T,(if u=p then 1 else 0 : Nat))=1 := by simp [pt]
    rw [ind] at r
    change t≤11 at r
    simp [edge]
    omega
  · let U := T.erase p
    let f := ∑ u∈U,missGhost E g h u
    let z := (U.filter (fun x=>missGhost E g h x=2)).card
    let fp := missGhost E g h p
    have rf (u : V) : row E J u+missGhost E g h u=2 := by
      rw [rowJ]; unfold missGhost
      split <;> split <;> simp_all
    have feq : t+f+fp=20 := by
      have q := sum_congr (s₂:=T) rfl (fun u _=>rf u)
      rw [sum_add_distrib,sum_const,tc] at q
      have e := sum_erase_add (s:=T) (f:=missGhost E g h) pt
      change f+fp=∑ u∈T,missGhost E g h u at e
      change t+(∑ u∈T,missGhost E g h u)=20 at q
      omega
    have up (u : V) (hu : u∈U) : u≠p := (mem_erase.mp hu).1
    have uT : U⊆T := erase_subset _ _
    have sp := split_directed_general E sym T {p} (singleton_subset_iff.mpr pt)
    have sdiff : T\{p}=U := by ext x; simp [U,and_comm]
    rw [sdiff,sum_singleton] at sp
    change d≤2*row E T p+∑ u∈U,row E U u at sp
    have cp := cap p pt
    simp only [ite_true,show insert g (insert h T)=S from rfl,split] at cp
    have rp := rf p
    change row E J p+fp=2 at rp
    have marked := marked_two_ghost_cut E sym S U (fun u hu=>into u (uT hu))
      g h gs hs (fun hu=>gt (uT hu)) (fun hu=>ht (uT hu))
      (by intro u hu; simpa [S,up u hu] using cap u (uT hu))
      (by
        intro x y xU yU xy
        exact ⟨fun h=>tf x (into x (uT xU)) y (into y (uT yU)) g gs (up x xU) (up y yU) gp xy h.1 h.2,
          fun e=>tf x (into x (uT xU)) y (into y (uT yU)) h hs (up x xU) (up y yU) hp xy e.1 e.2⟩)
    change (∑ u∈U,row E U u)≤2*(f+z) ∧ 2*z≤f at marked
    simp [edge]
    omega

#print axioms a11_core_simple_owner_bound
end Erdos151N62
