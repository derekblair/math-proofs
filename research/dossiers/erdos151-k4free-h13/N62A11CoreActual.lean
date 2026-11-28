import N62A11CoreGraph
import N62DoubleRow

namespace Erdos151N62
open Erdős151 Erdős151.Upper Erdos151H12 Erdos151H13 Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]
variable {S X : Finset V}

theorem a11_core_actual_owner_bound
    (F : NearOwnerFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V)) (out : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (T : Finset V) (g h : V) (gt : g∉T) (ht : h∉T) (gh : g≠h)
    (tc : T.card=10) (se : S=insert g (insert h T))
    (p : V) (pt : p∈T) (marks : F.marks=S.erase p)
    (cap : ∀ u∈T,(Dstar G F u).card≤3+(if u=p then 1 else 0)) :
    F.doubles.card≤23 := by
  classical
  let E := DoubleRel G F
  have inj := all_pair_support_inj G F sym irr sc sf out upper (by
    intro z dz
    obtain ⟨_,a,as,b,bs,ab,_,_,eq⟩ := F.dblData z dz
    by_cases ap : a=p
    · exact ⟨b,by rw [marks]; exact mem_erase.mpr ⟨fun bp=>ab (ap.trans bp.symm),bs⟩,by simp [eq]⟩
    · exact ⟨a,by rw [marks]; exact mem_erase.mpr ⟨ap,as⟩,by simp [eq]⟩)
  have rowEq (u : V) (uS : u∈S) : (Dstar G F u).card=row E S u := by
    apply Dstar_count_of_relation G F sym uS T
    intro x hx y hy e
    exact inj (mem_filter.mp hx).1 (mem_filter.mp hy).1 e
  have cE : ∀ u∈T,row E (insert g (insert h T)) u≤3+(if u=p then 1 else 0) := by
    intro u hu
    rw [←se,←rowEq]
    · exact cap u hu
    · simp [se,hu]
  have tf : ∀ a∈insert g (insert h T), ∀ b∈insert g (insert h T), ∀ c∈insert g (insert h T),
      a≠p → b≠p → c≠p → E a b → E a c → E b c → False := by
    intro a ha b hb c hc ap bp cp ab ac bc
    apply marked_drel_triangle_free G F sym irr sc sf out upper _ _ _ ab ac bc
    all_goals rw [marks,mem_erase,se]; exact ⟨by assumption,by assumption⟩
  have bound := a11_core_simple_owner_bound E (fun {_ _} t => drel_sym G F t)
    (fun u t => drel_ne G F t rfl) T g h gt ht gh tc p pt cE tf
  rw [←se] at bound
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
  change (∑ u∈S,row E S u)=2*F.doubles.card at count
  omega

#print axioms a11_core_actual_owner_bound
end Erdos151N62
