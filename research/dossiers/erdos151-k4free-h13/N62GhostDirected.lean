import N62TwoGhostCut

namespace Erdos151N62
open Erdős151.Upper Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (E : V→V→Prop) [DecidableRel E]

theorem ghost_directed_counts
    (sym : ∀ {a b}, E a b → E b a) (irr : ∀ a, ¬E a a)
    (T : Finset V) (g h : V) (gt : g∉T) (ht : h∉T) (gh : g≠h) :
    let S := insert g (insert h T)
    let J : Finset V := {g,h}
    let d := ∑ u∈T,row E T u
    let t := ∑ u∈T,row E J u
    (∀ u, row E S u=row E T u+row E J u) ∧
    (∀ u, row E J u = (if E u g then 1 else 0)+(if E u h then 1 else 0)) ∧
    t=row E T g+row E T h ∧
    (∑ u∈S,row E S u)=d+2*t+2*(if E g h then 1 else 0) := by
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
  refine ⟨split,rowJ,tCross,full⟩

#print axioms ghost_directed_counts
end Erdos151N62
