import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Pairwise
import Lean.Elab.Tactic.Omega

namespace DirectedKDSP

variable {V Label Color : Type*} [DecidableEq V] [DecidableEq Color]

/-- Private vertices cannot conflict across original labelled supports. -/
theorem disjoint_of_shared_colors (support used : Label → Finset V)
    (shared : Finset V) (color : V → Color)
    (memSupport : ∀ i, used i ⊆ support i)
    (memShared : ∀ {i j}, i ≠ j → ∀ {v}, v ∈ support i → v ∈ support j → v ∈ shared)
    (colorsDisjoint : ∀ {i j}, i ≠ j →
      Disjoint ((used i ∩ shared).image color) ((used j ∩ shared).image color))
    {i j : Label} (different : i ≠ j) : Disjoint (used i) (used j) := by
  apply Finset.disjoint_left.mpr
  intro v hi hj
  have h := memShared different (memSupport i hi) (memSupport j hj)
  exact Finset.disjoint_left.mp (colorsDisjoint different)
    (Finset.mem_image.mpr ⟨v, Finset.mem_inter.mpr ⟨hi,h⟩,rfl⟩)
    (Finset.mem_image.mpr ⟨v, Finset.mem_inter.mpr ⟨hj,h⟩,rfl⟩)

private def usedUnion (a : List (Finset V)) : Finset V :=
  a.foldr (· ∪ ·) ∅

private def usedDegree (a : List (Finset V)) : Nat :=
  (a.map Finset.card).sum

/-- Covering a set in exactly its cardinality number of vertex visits
is equivalent to pairwise disjointness, even with a dummy filler set. -/
theorem exact_cover_cardinality (a : List (Finset V)) :
    (usedUnion a).card ≤ usedDegree a ∧
    ((usedUnion a).card = usedDegree a ↔ a.Pairwise Disjoint) := by
  induction a with
  | nil => simp [usedUnion,usedDegree]
  | cons s rest ih =>
    obtain ⟨le,property⟩ := ih
    have inter := Finset.card_union_add_card_inter s (usedUnion rest)
    have fold : ∀ v, v ∈ usedUnion rest ↔ ∃ t ∈ rest, v ∈ t := by
      intro v
      clear le property inter
      induction rest with
      | nil => simp [usedUnion]
      | cons t tail j => simp [usedUnion, List.foldr_cons] at j ⊢; aesop
    change (s ∪ usedUnion rest).card ≤ s.card + usedDegree rest ∧
      ((s ∪ usedUnion rest).card = s.card + usedDegree rest ↔ (s::rest).Pairwise Disjoint)
    refine ⟨by omega,?_⟩
    rw [List.pairwise_cons]
    constructor
    · intro eq
      have z : (s ∩ usedUnion rest).card=0 := by omega
      have dis : Disjoint s (usedUnion rest) :=
        Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp z)
      refine ⟨?_,property.mp (by omega)⟩
      intro t ht
      apply Finset.disjoint_left.mpr
      intro v hv hvt
      exact Finset.disjoint_left.mp dis hv ((fold _).mpr ⟨t,ht,hvt⟩)
    · rintro ⟨dis,p⟩
      have unionDis : Disjoint s (usedUnion rest) := by
        apply Finset.disjoint_left.mpr
        intro v hs hu
        obtain ⟨t,ht,hvt⟩ := (fold v).mp hu
        exact Finset.disjoint_left.mp (dis t ht) hs hvt
      rw [Finset.card_union_of_disjoint unionDis, property.mpr p]

#print axioms disjoint_of_shared_colors
#print axioms exact_cover_cardinality
end DirectedKDSP
