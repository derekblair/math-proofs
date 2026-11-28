import N62DCounts
import N62DoubleRow

namespace Erdos151N62
open Erdős151 Erdős151.Upper Erdos151H12 Erdos151H13 Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]
variable {S X : Finset V}

theorem drel_total_of_injective (F : NearOwnerFrame G S X)
    [DecidableRel (DoubleRel G F)]
    (sym : ∀ {a b}, G a b → G b a)
    (inj : Set.InjOn (support G S) (F.doubles : Set V)) :
    (∑ u∈S,row (DoubleRel G F) S u)=2*F.doubles.card := by
  classical
  let E := DoubleRel G F
  have rowEq (u : V) (uS : u∈S) : (Dstar G F u).card=row E S u := by
    apply Dstar_count_of_relation G F sym uS S
    intro x hx y hy e
    exact inj (mem_filter.mp hx).1 (mem_filter.mp hy).1 e
  have count := dstar_count_on G F sym S (Subset.rfl)
  have only2 (z : V) (zd : z∈F.doubles) : (support G S z∩S).card=2 := by
    have hs : support G S z⊆S := filter_subset _ _
    rw [inter_eq_left.mpr hs]
    exact support_two G F zd
  have one : degreeBucket G F S 1=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨zd,e⟩ := (mem_degreeBucket G F S 1 z).mp hz
    have t := only2 z zd
    omega
  have two : degreeBucket G F S 2=F.doubles := by
    ext z
    rw [mem_degreeBucket]
    exact ⟨And.left,fun h=>⟨h,only2 z h⟩⟩
  rw [one,two,card_empty,zero_add] at count
  have conv := sum_congr (s₂:=S) rfl rowEq
  rw [conv] at count
  exact count

#print axioms drel_total_of_injective
end Erdos151N62
