import N62PrivateColumns
import N62PrivateCases

namespace Erdos151N62
open Erdős151 Erdos151H12 Erdos151H13
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]

noncomputable def acnt (S X : Finset V) := (weightedSet X (Acol G S)).card
noncomputable def bcnt (S X : Finset V) := (weightedSet X (Bcol G S)).card
noncomputable def ccnt (S X : Finset V) := (weightedSet X (Ccol G S)).card
noncomputable def dcnt (S X : Finset V) := (weightedSet X (Dcol G S)).card

theorem exact_private_special_counts (S X : Finset V) :
    (privateColumns G S X).card=acnt G S X+bcnt G S X+ccnt G S X ∧
    (specialCols G S X).card=acnt G S X+dcnt G S X := by
  classical
  let A := weightedSet X (Acol G S)
  let B := weightedSet X (Bcol G S)
  let C := weightedSet X (Ccol G S)
  let D := weightedSet X (Dcol G S)
  have aBc : Disjoint A B := Finset.disjoint_left.mpr (by
    intro x ha hb
    have e : ncol G S x=1 := (Finset.mem_filter.mp ha).2
    have f : ncol G S x=2 := ((Finset.mem_filter.mp hb).2 : Bcol G S x).1
    omega)
  have aCc : Disjoint A C := Finset.disjoint_left.mpr (by
    intro x ha hc
    have e : ncol G S x=1 := (Finset.mem_filter.mp ha).2
    have f : ncol G S x=2 := ((Finset.mem_filter.mp hc).2 : Ccol G S x).1
    omega)
  have aDc : Disjoint A D := Finset.disjoint_left.mpr (by
    intro x ha hd
    have e : ncol G S x=1 := (Finset.mem_filter.mp ha).2
    have f : ncol G S x=2 := ((Finset.mem_filter.mp hd).2 : Dcol G S x).1
    omega)
  have bCc : Disjoint B C := Finset.disjoint_left.mpr (by
    intro x hb hc
    have e := ((Finset.mem_filter.mp hb).2 : Bcol G S x).2
    have f := ((Finset.mem_filter.mp hc).2 : Ccol G S x).2
    omega)
  have p : privateColumns G S X=(A∪B)∪C := by
    ext x
    simp [privateColumns,weightedSet,A,B,C]
    tauto
  have s : specialCols G S X=A∪D := by
    ext x
    simp [specialCols,weightedSet,A,D]
    tauto
  change (privateColumns G S X).card=A.card+B.card+C.card ∧
    (specialCols G S X).card=A.card+D.card
  rw [p,s,Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨aCc,bCc⟩),
    Finset.card_union_of_disjoint aBc,Finset.card_union_of_disjoint aDc]
  exact ⟨rfl,rfl⟩

theorem exact_lone_column_lower (S X : Finset V)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (sf : Free (Forbidden G) (S : Set V))
    (blocked : ∀ x∈X, ¬Free (Forbidden G) (insert x (S : Set V))) :
    acnt G S X+ccnt G S X+2*dcnt G S X≤∑ x∈X,lcol G S x := by
  classical
  let a (x : V) := if Acol G S x then (1:Nat) else 0
  let c (x : V) := if Ccol G S x then (1:Nat) else 0
  let d (x : V) := if Dcol G S x then (2:Nat) else 0
  have h := Finset.sum_le_sum (s:=X) (f:=fun x => a x+c x+d x) (fun x hx => by
    have hh := (blocked_degreeTen_local G S sym irr sf x (blocked x hx)).2.2.1
    change a x + c x + 2*(if Dcol G S x then 1 else 0) ≤ _ at hh
    by_cases hd : Dcol G S x <;> simpa [d,hd] using hh)
  simp only [Finset.sum_add_distrib] at h
  have aa : acnt G S X=∑ x∈X,a x := by
    have e := indicator_count X (Acol G S) 1
    simpa [acnt,a] using e
  have cc : ccnt G S X=∑ x∈X,c x := by
    have e := indicator_count X (Ccol G S) 1
    simpa [ccnt,c] using e
  have dd : 2*dcnt G S X=∑ x∈X,d x := by
    exact indicator_count X (Dcol G S) 2
  omega

#print axioms exact_private_special_counts
#print axioms exact_lone_column_lower
end Erdos151N62
