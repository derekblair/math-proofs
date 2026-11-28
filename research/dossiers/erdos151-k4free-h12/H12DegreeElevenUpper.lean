import H12DegreeTenUpper

namespace Erdos151H12
open Erdős151 Erdős151.Upper
open scoped BigOperators
variable {V : Type*} [DecidableEq V] [Fintype V] (G C : V → V → Prop)
variable [DecidableRel G] [DecidableRel C]

theorem degreeEleven_upper_slots
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (sub : ∀ {a b}, C a b → G a b) (two : TwoTriangles C)
    (degree : ∀ v, (neighbors G v).card ≤ 11)
    (w : V) (h11 : (neighbors G w).card = 11)
    (cmin : ∀ u∈neighbors C w, 8 ≤ (neighbors C u).card)
    (e : Nat) (he : ∑ u∈neighbors C w,row C (neighbors C w) u = 2*e) :
    (∑ x∈ext (neighbors G w) w,ncol G (neighbors G w) x) + 2*e ≤ 110 ∧
    (∑ x∈ext (neighbors G w) w,lcol G (neighbors G w) x) + 7*(neighbors C w).card ≤ 110 := by
  classical
  let S := neighbors G w
  let T := neighbors C w
  let X := ext S w
  have hTS : T ⊆ S := fun _ hx => (mem_neighbors G).mpr (sub ((mem_neighbors C).mp hx))
  have hhw : w ∉ S := fun hw => irr w ((mem_neighbors G).mp hw)
  have hTT : T.card ≤ S.card := Finset.card_le_card hTS
  have coreNotLone {u v : V} (h : C u v) : ¬ Lone G u v := by
    obtain ⟨x,_,_,hx,hy,_,_⟩ := two u v h
    exact fun he => he.2 x ⟨sub hx,sub hy⟩
  have hrow (u : V) (hu : u∈S) : row G X u + row G S u + 1 = (neighbors G u).card :=
    row_degree G sym w u hu hhw
  have hdegS : (∑ u∈S,(neighbors G u).card) ≤ 121 := by
    have hsum := Finset.sum_le_sum (s:=S) (fun u _ => degree u)
    simpa [show S.card = 11 from h11] using hsum
  have hf : (∑ u∈S,(neighbors G u).card) = (∑ u∈S,row G X u) + (∑ u∈S,row G S u) + S.card := by
    rw [show S.card = ∑ _u∈S,(1:Nat) by simp,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun u hu => (hrow u hu).symm)
  have heC : (∑ u∈T,row C T u) ≤ ∑ u∈S,row G S u := by
    calc
      _ ≤ ∑ u∈T,row G S u := Finset.sum_le_sum (fun u _ =>
        Finset.card_le_card (fun x hx => Finset.mem_filter.mpr
          ⟨hTS (Finset.mem_filter.mp hx).1,sub (Finset.mem_filter.mp hx).2⟩))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hTS (by intros; omega)
  change (∑ u∈T,row C T u) = 2*e at he
  change S.card = 11 at h11
  change (∑ x∈X,ncol G S x)+2*e≤110 ∧ (∑ x∈X,lcol G S x)+7*T.card≤110
  refine ⟨?_,?_⟩
  · rw [ncol_eq_incidence G S X sym,transpose]
    omega
  · letI : DecidableRel (Lone G) := fun _ _ => Classical.propDecidable _
    have hL_S (u : V) (hu : u∈S) : row (Lone G) X u ≤ 10 := by
      have hl : row (Lone G) X u ≤ row G X u :=
        Finset.card_le_card (fun x hx => Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2.1⟩)
      have hr := hrow u hu
      have hh := degree u
      omega
    have hL_T (u : V) (hu : u∈T) : row (Lone G) X u ≤ 3 := by
      let F := X.filter (Lone G u)
      have hdis : Disjoint F (neighbors C u) := Finset.disjoint_left.mpr (fun x hx hxn =>
        coreNotLone ((mem_neighbors C).mp hxn) (Finset.mem_filter.mp hx).2)
      have hsub : (F ∪ neighbors C u) ⊆ neighbors G u := by
        intro x hx
        rcases Finset.mem_union.mp hx with hp|hq
        · exact (mem_neighbors G).mpr (Finset.mem_filter.mp hp).2.1
        · exact (mem_neighbors G).mpr (sub ((mem_neighbors C).mp hq))
      have hh := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdis] at hh
      change F.card ≤ 3
      have h0 := degree u
      have h1 := cmin u hu
      omega
    have hcap := split_cap S T hTS (row (Lone G) X) 3 10 hL_T hL_S
    rw [lcol_eq_incidence G S X sym,transpose]
    omega

#print axioms degreeEleven_upper_slots
end Erdos151H12
