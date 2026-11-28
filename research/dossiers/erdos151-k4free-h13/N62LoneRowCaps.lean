import N62LoneExhaustion

namespace Erdos151N62
open Erdős151 Erdős151.Upper Erdos151H12 Erdos151H13 Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G C : V→V→Prop)
variable [DecidableRel G] [DecidableRel C]

theorem tight_lone_row_caps
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (sub : ∀ {a b}, C a b → G a b) (two : TwoTriangles C)
    (deg : ∀ v, (neighbors G v).card≤12)
    (w : V) (s12 : (neighbors G w).card=12) (t10 : (neighbors C w).card=10)
    (hmin : ∀ u∈neighbors C w, 8≤(neighbors C u).card) :
    let S := neighbors G w
    let T := neighbors C w
    let X := ext S w
    (∀ u∈S, ambientLoneRow G X u ≤ 11) ∧
    (∀ u∈T, ambientLoneRow G X u ≤ 4) ∧
    ((∑ x∈X,lcol G S x)=62 → ∀ u∈S\T, ambientLoneRow G X u=11) := by
  classical
  let S := neighbors G w
  let T := neighbors C w
  let X := ext S w
  have ts : T⊆S := fun _ hu => (mem_neighbors G).mpr (sub ((mem_neighbors C).mp hu))
  have hw : w∉S := fun h => irr w ((mem_neighbors G).mp h)
  have cap (u : V) (hu : u∈S) : ambientLoneRow G X u≤11 := by
    have h := row_degree G sym w u hu hw
    have d := deg u
    have l : ambientLoneRow G X u ≤ row G X u :=
      card_le_card (fun x hx => mem_filter.mpr
        ⟨(mem_filter.mp hx).1,(mem_filter.mp hx).2.1⟩)
    change row G X u + row G S u + 1=(neighbors G u).card at h
    omega
  have small (u : V) (hu : u∈T) : ambientLoneRow G X u≤4 := by
    let Y := X.filter (Lone G u)
    have dis : Disjoint Y (neighbors C u) := by
      apply Finset.disjoint_left.mpr
      intro z hz hc
      obtain ⟨v,_,_,hv,hv',_,_⟩ := two u z ((mem_neighbors C).mp hc)
      exact (mem_filter.mp hz).2.2 v ⟨sub hv,sub hv'⟩
    have xu : Y ∪ neighbors C u ⊆ neighbors G u := by
      intro z hz
      rcases mem_union.mp hz with h|h
      · exact (mem_neighbors G).mpr (mem_filter.mp h).2.1
      · exact (mem_neighbors G).mpr (sub ((mem_neighbors C).mp h))
    have h := card_le_card xu
    rw [card_union_of_disjoint dis] at h
    have d := deg u
    have k := hmin u hu
    change Y.card≤4
    omega
  refine ⟨cap,small,?_⟩
  intro l62 g hg
  have ls := lcol_eq_incidence G S X sym
  rw [transpose] at ls
  change (∑ x∈X,lcol G S x)=∑ u∈S,ambientLoneRow G X u at ls
  have f : (S\T).card=2 := by rw [card_sdiff_of_subset ts,s12,t10]
  have one : (((S\T).erase g)).card=1 := by rw [card_erase_of_mem hg,f]
  have p1 := sum_le_sum (s:=T) (g:=fun _=>4) small
  have p2 := sum_le_sum (s:=(S\T).erase g) (g:=fun _=>11)
    (fun u hu=>cap u (mem_sdiff.mp (mem_of_mem_erase hu)).1)
  have e1 := sum_sdiff ts (f:=ambientLoneRow G X)
  have e2 := sum_erase_add (s:=S\T) (f:=ambientLoneRow G X) hg
  simp only [sum_const,nsmul_eq_mul,show T.card=10 from t10,one] at p1 p2
  have gcap := cap g (mem_sdiff.mp hg).1
  change (∑ x∈X,lcol G S x)=62 at l62
  change ambientLoneRow G X g=11
  omega

#print axioms tight_lone_row_caps
end Erdos151N62
