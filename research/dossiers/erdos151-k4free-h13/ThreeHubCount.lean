import H12AdjacentPrice
import Mathlib.Data.Finset.SDiff
import Mathlib.Tactic.Tauto

namespace Erdos151H13
open Erdos151H12
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Inclusion-exclusion in a subtraction-free form. -/
theorem three_union_card (A B C : Finset V) :
  ((A ∪ B) ∪ C).card + (A ∩ B).card + (A ∩ C).card + (B ∩ C).card =
    A.card+B.card+C.card+((A ∩ C) ∩ (B ∩ C)).card := by
  have m1 := Finset.card_union_add_card_inter A B
  have m2 := Finset.card_union_add_card_inter (A ∪ B) C
  have m3 := Finset.card_union_add_card_inter (A ∩ C) (B ∩ C)
  have eq : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
    ext v
    simp only [Finset.mem_inter,Finset.mem_union]
    tauto
  rw [eq] at m2
  omega

/-- A shared outer site costs at most one original incidence:
double contributors may be deduplicated, not also deleted. -/
theorem outer_retention_count (A B S E : Finset V)
    (shared : A ∩ B ⊆ S)
    (keepBoth : A ∩ B ⊆ E)
    (keepOutside : (A ∪ B) \ S ⊆ E) :
    A.card + B.card ≤ E.card + S.card := by
  let C := (A ∪ B) \ S
  let M := A ∩ B
  have dis : Disjoint C M := by
    apply Finset.disjoint_left.mpr
    intro v vc vm
    exact (Finset.mem_sdiff.mp vc).2 (shared vm)
  have hs : C ∪ M ⊆ E := by
    intro v hv
    exact (Finset.mem_union.mp hv).elim (fun h => keepOutside h) (fun h => keepBoth h)
  have h := Finset.card_le_card hs
  rw [Finset.card_union_of_disjoint dis] at h
  have m := Finset.card_sdiff_add_card_inter (A ∪ B) S
  change C.card + ((A ∪ B) ∩ S).card = (A ∪ B).card at m
  have atop : ((A∪B) ∩ S).card ≤ S.card :=
    Finset.card_le_card (by intro v hv; exact (Finset.mem_inter.mp hv).2)
  have b := Finset.card_union_add_card_inter A B
  change (A∪B).card+M.card=A.card+B.card at b
  omega

#print axioms outer_retention_count

variable (G : V → V → Prop) [DecidableRel G]

/-- For hubs on two ambient edges x–w and w–y, the triple overlap
cancels against the part of the outer overlap inside the center link.
The four within-hub directed incidences appear as a +4 offset. -/
theorem three_hub_external_union
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (x w y : V) (xw : G x w) (wy : G w y)
    (xwne : x ≠ w) (xyne : x ≠ y) (wyne : w ≠ y) :
    let A := neighbors G x
    let B := neighbors G y
    let C := neighbors G w
    let U := ((A ∪ B) ∪ C) \ ({x,w,y} : Finset V)
    let S := (A ∩ B) \ insert w C
    U.card + (A ∩ C).card + (B ∩ C).card + S.card + 4 =
      A.card+B.card+C.card := by
  let A := neighbors G x
  let B := neighbors G y
  let C := neighbors G w
  let H : Finset V := {x,w,y}
  let U := ((A ∪ B) ∪ C) \ H
  let S := (A ∩ B) \ insert w C
  change U.card + (A ∩ C).card + (B ∩ C).card + S.card + 4 =
      A.card+B.card+C.card
  have ha : w ∈ A := (mem_neighbors G).mpr xw
  have hb : w ∈ B := (mem_neighbors G).mpr (sym wy)
  have hx : x ∈ C := (mem_neighbors G).mpr (sym xw)
  have hy : y ∈ C := (mem_neighbors G).mpr wy
  have hwn : w ∉ C := fun h => irr _ ((mem_neighbors G).mp h)
  have hh : H ⊆ (A ∪ B) ∪ C := by
    intro v hv
    simp only [H,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl|rfl|rfl
    · exact Finset.mem_union_right _ hx
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ ha)
    · exact Finset.mem_union_right _ hy
  have hhc : H.card=3 := by
    simp [H,xwne,xyne,wyne,Finset.card_insert_of_notMem]
  have hU := Finset.card_sdiff_add_card_eq_card hh
  change U.card+H.card=((A∪B)∪C).card at hU
  have st : (A ∩ B) ∩ insert w C = insert w ((A ∩ C) ∩ (B ∩ C)) := by
    ext v
    simp only [Finset.mem_inter,Finset.mem_insert]
    constructor
    · tauto
    · rintro (rfl|h)
      · exact ⟨⟨ha,hb⟩,Or.inl rfl⟩
      · tauto
  have hS := Finset.card_sdiff_add_card_inter (A∩B) (insert w C)
  rw [st, Finset.card_insert_of_notMem (by simp [hwn])] at hS
  change S.card+(((A∩C)∩(B∩C)).card+1)=(A∩B).card at hS
  have e := three_union_card A B C
  omega

#print axioms three_union_card
#print axioms three_hub_external_union
end Erdos151H13
